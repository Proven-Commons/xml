/-
  The XML tree type for the safe subset, the canonical printer, and
  the well formed predicate that the round trip proof in `Proofs`
  uses.

  The subset is XML 1.0 narrowed as `SPEC.md` states: elements,
  attributes, text, comments, and processing instructions, with
  character references and CDATA sections read as character data.
  There is no document type declaration, no entity beyond the five
  predefined ones, no namespace (so no attribute named `xmlns`), and
  no XML declaration.

  A node is one of:

  - `text`: a run of character data, held as a list of characters.
    Text written as plain characters, as character references, and
    as CDATA sections all lands here as one run: the three are
    spellings of the same character data, not different trees.
  - `elem`: an element: a name, a list of attribute name and value
    pairs in the order held, and a list of content nodes.
  - `comment`: a comment, held as the characters between the marks.
  - `pi`: a processing instruction: a target name and the data
    after it, held as characters.

  A document is a list of prolog nodes (comments and processing
  instructions only), one root element, and a list of epilog nodes.

  Attribute values are held normalized, the way the parser reads
  them: a literal tab or newline in the source is a space in the
  value, and the five predefined entities and the character
  references are the characters they stand for.
-/

namespace Xml

/-- A node in a document or in element content. -/
inductive Node where
  | text (cs : List Char)
  | elem (name : List Char) (attrs : List (List Char × List Char))
    (content : List Node)
  | comment (cs : List Char)
  | pi (target : List Char) (data : List Char)

/-- A document: prolog, one root element, epilog. -/
structure Document where
  prolog : List Node
  root : Node
  epilog : List Node

/-! ## Characters and names -/

/-- A legal XML character, as a proposition, in code points: tab,
    line feed, carriage return, then the ranges of the XML 1.0
    character production. A Lean `Char` is a Unicode scalar value,
    so no character here can be half of a surrogate pair; the
    surrogate range is excluded all the same, since a character
    reference can name it. -/
def LegalChar (c : Char) : Prop :=
  c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 13 ∨
    (0x20 ≤ c.toNat ∧ c.toNat ≤ 0xD7FF) ∨
    (0xE000 ≤ c.toNat ∧ c.toNat ≤ 0xFFFD) ∨
    (0x10000 ≤ c.toNat ∧ c.toNat ≤ 0x10FFFF)

/-- The legal character test the parser runs. -/
def isLegalChar (c : Char) : Bool :=
  decide (c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 13 ∨
    (0x20 ≤ c.toNat ∧ c.toNat ≤ 0xD7FF) ∨
    (0xE000 ≤ c.toNat ∧ c.toNat ≤ 0xFFFD) ∨
    (0x10000 ≤ c.toNat ∧ c.toNat ≤ 0x10FFFF))

theorem isLegalChar_iff {c : Char} : isLegalChar c = true ↔ LegalChar c := by
  simp only [isLegalChar, LegalChar, decide_eq_true_eq]

/-- The first character of a name in the subset: an ASCII letter or
    an underscore. The colon is not a name character in this
    subset, since namespaces are out. -/
def IsNameStart (c : Char) : Prop :=
  ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ c = '_'

/-- A later character of a name: a name start character, a digit, a
    hyphen, or a point. -/
def IsNameChar (c : Char) : Prop :=
  IsNameStart c ∨ ('0' ≤ c ∧ c ≤ '9') ∨ c = '-' ∨ c = '.'

/-- The name start test the parser runs. -/
def isNameStart (c : Char) : Bool :=
  decide (('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ c = '_')

theorem isNameStart_iff {c : Char} : isNameStart c = true ↔ IsNameStart c := by
  simp only [isNameStart, IsNameStart, decide_eq_true_eq]

/-- The name character test the parser runs. -/
def isNameChar (c : Char) : Bool :=
  decide ((('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ c = '_') ∨
    ('0' ≤ c ∧ c ≤ '9') ∨ c = '-' ∨ c = '.')

theorem isNameChar_iff {c : Char} : isNameChar c = true ↔ IsNameChar c := by
  simp only [isNameChar, IsNameChar, IsNameStart, decide_eq_true_eq]

/-- A name that follows the subset rule: a name start character,
    then name characters. -/
def ValidName (cs : List Char) : Prop :=
  ∃ c ds, cs = c :: ds ∧ IsNameStart c ∧ ∀ x ∈ ds, IsNameChar x

/-- Whitespace in XML: space, tab, line feed, carriage return, as a
    proposition. -/
def IsWs (c : Char) : Prop :=
  c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'

/-- No two dashes in a row anywhere in the list, stated as: the
    list is never a part, then two dashes, then a part. The body of
    a comment must satisfy this. -/
def NoDashDash (cs : List Char) : Prop :=
  ∀ pre suf, cs ≠ pre ++ '-' :: '-' :: suf

/-- The list does not end with a dash. The body of a comment must
    also satisfy this, or the closing marks run into the body. -/
def NotDashEnd (cs : List Char) : Prop :=
  ∀ pre, cs ≠ pre ++ ['-']

/-- No `?>` anywhere in the list, stated as: the list is never a
    part, then a question mark and a greater sign, then a part.
    The data of a processing instruction must satisfy this. -/
def NoQClose (cs : List Char) : Prop :=
  ∀ pre suf, cs ≠ pre ++ '?' :: '>' :: suf

/-- A processing instruction target is reserved when it is the word
    `xml`, in any case. A document whose first processing
    instruction target is `xml` is the XML declaration form, which
    this subset does not hold. -/
def IsXmlTarget (t : List Char) : Prop :=
  t.map Char.toLower = ['x', 'm', 'l']

/-! ## The printer -/

/-- The printed form of one character of character data. The
    ampersand, the less sign, and the greater sign are written as
    the predefined entities, so a printed text can never hold the
    forbidden `]]>` run. A carriage return is written as a
    character reference, so it reads back as itself. Every other
    character is written as it is. -/
def escapeTextChar (c : Char) : List Char :=
  if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if c = '<' then ['&', 'l', 't', ';']
  else if c = '>' then ['&', 'g', 't', ';']
  else if c = '\r' then ['&', '#', '1', '3', ';']
  else [c]

/-- The printed form of a run of character data. -/
def escapeText (cs : List Char) : List Char :=
  cs.flatMap escapeTextChar

/-- The printed form of one character of an attribute value. The
    ampersand and the less sign are written as entities, the quote
    as an entity, and tab, line feed, and carriage return as
    character references, because a literal one of those three
    would read back as a space under the parser's normalization.
    Every other character is written as it is. -/
def escapeAttrChar (c : Char) : List Char :=
  if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if c = '<' then ['&', 'l', 't', ';']
  else if c = '"' then ['&', 'q', 'u', 'o', 't', ';']
  else if c = '\t' then ['&', '#', '9', ';']
  else if c = '\n' then ['&', '#', '1', '0', ';']
  else if c = '\r' then ['&', '#', '1', '3', ';']
  else [c]

/-- The printed form of an attribute value, without the quotes. -/
def escapeAttr (cs : List Char) : List Char :=
  cs.flatMap escapeAttrChar

/-- The printed form of the attribute list: each pair preceded by
    one space, the name, an equals sign, and the value in double
    quotes. -/
def printAttrs : List (List Char × List Char) → List Char
  | [] => []
  | (k, v) :: rest =>
    ' ' :: k ++ ('=' :: '"' :: (escapeAttr v ++ '"' :: printAttrs rest))

mutual
/-- The canonical printed form of a node. An element with no
    content prints in the short form. A processing instruction with
    no data prints with no space before the closing marks. -/
def printNode : Node → List Char
  | .text cs => escapeText cs
  | .elem name attrs content => printElem name attrs content
  | .comment cs => '<' :: '!' :: '-' :: '-' :: (cs ++ '-' :: '-' :: '>' :: [])
  | .pi t d =>
    '<' :: '?' ::
      (t ++ (if d = [] then ['?', '>'] else ' ' :: d ++ ['?', '>']))

/-- An element in its printed form: the start tag, then the
    content and the end tag, or the short form when the content is
    empty. -/
def printElem (name : List Char) (attrs : List (List Char × List Char))
    (content : List Node) : List Char :=
  '<' :: (name ++ printAttrs attrs ++
    (if content = [] then ['/', '>']
     else '>' :: (printNodes content ++ '<' :: '/' :: (name ++ ['>']))))

/-- A list of nodes in its printed form, one after another. -/
def printNodes : List Node → List Char
  | [] => []
  | n :: ns => printNode n ++ printNodes ns
end

/-- A document in its printed form. -/
def print (d : Document) : List Char :=
  printNodes d.prolog ++ printNode d.root ++ printNodes d.epilog

/-! ## Well formed trees -/

/-- The attribute name `xmlns`. In Namespaces in XML 1.0 it
    declares a default namespace (`DefaultAttName ::= 'xmlns'`).
    It has no colon, so the colon ban on names does not keep it
    out; this subset has no namespaces, so no attribute may carry
    this exact name. Other names, such as `xmlnsx` or `XMLNS`, are
    ordinary names: they declare nothing. -/
def xmlnsName : List Char := ['x', 'm', 'l', 'n', 's']

/-- Attribute lists the printer can write and the parser reads
    back: each name is a valid name and not `xmlns`, each value
    holds only legal characters, no name appears twice, and the
    rest of the list is in order. -/
def AttrsOk : List (List Char × List Char) → Prop
  | [] => True
  | kv :: rest =>
    ValidName kv.1 ∧ kv.1 ≠ xmlnsName ∧ (∀ c ∈ kv.2, LegalChar c) ∧
      (∀ kv2 ∈ rest, kv2.1 ≠ kv.1) ∧ AttrsOk rest

mutual
/-- A node the printer can write and the parser reads back as the
    same node. A text run is not empty and holds only legal
    characters. A comment body has no two dashes in a row, does not
    end with a dash, holds only legal characters, and holds no
    carriage return. A processing instruction has a valid target
    that is not the reserved word, and data that holds no `?>`,
    holds only legal characters, does not start with whitespace
    (the printer writes one space before the data, and the parser
    skips whitespace there, so a data value starting with
    whitespace would lose it), and holds no carriage return.

    The carriage return rule: the parser normalizes line ends
    before reading, so a literal carriage return reads as a line
    feed. Text and attribute values can still hold one, written as
    the character reference `&#13;`, but a comment or processing
    instruction has no references, so neither can hold one after
    parsing, and the printer could not write one back. -/
inductive WFNode : Node → Prop where
  | text {cs : List Char} (hne : cs ≠ []) (hlegal : ∀ c ∈ cs, LegalChar c) :
      WFNode (.text cs)
  | elem {name : List Char} {attrs : List (List Char × List Char)}
      {content : List Node} (hname : ValidName name) (hattrs : AttrsOk attrs)
      (hcontent : WFNodes content) : WFNode (.elem name attrs content)
  | comment {cs : List Char} (hdd : NoDashDash cs) (hde : NotDashEnd cs)
      (hlegal : ∀ c ∈ cs, LegalChar c) (hcr : '\r' ∉ cs) :
      WFNode (.comment cs)
  | pi {t d : List Char} (hname : ValidName t) (hres : ¬ IsXmlTarget t)
      (hq : NoQClose d) (hlegal : ∀ c ∈ d, LegalChar c)
      (hstart : d = [] ∨ ∀ c cs, d = c :: cs → ¬ IsWs c)
      (hcr : '\r' ∉ d) :
      WFNode (.pi t d)

/-- A content list whose nodes are all well formed, with no two
    text runs next to each other: the parser merges the character
    data between two marks into one run, so a tree with two text
    runs side by side would print to a text the parser reads back
    as one run. -/
inductive WFNodes : List Node → Prop where
  | nil : WFNodes []
  | cons {n : Node} {ns : List Node} (hn : WFNode n) (hns : WFNodes ns)
      (hadj : (∃ cs, n = .text cs) → ∀ cs, ns.head? ≠ some (.text cs)) :
      WFNodes (n :: ns)
end

/-- A node in a prolog or an epilog: a comment or a processing
    instruction, and well formed. -/
def MiscOk (ns : List Node) : Prop :=
  ∀ n ∈ ns, WFNode n ∧
    ((∃ cs, n = .comment cs) ∨ (∃ t d, n = .pi t d))

/-- A document the printer can write and the parser reads back:
    prolog and epilog hold only comments and processing
    instructions, and the root is an element. -/
def WF (d : Document) : Prop :=
  MiscOk d.prolog ∧ WFNode d.root ∧
    (∃ name attrs content, d.root = .elem name attrs content) ∧
    MiscOk d.epilog

end Xml
