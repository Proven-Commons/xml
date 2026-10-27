/-
  The XML parser for the safe subset. It reads a list of characters
  and returns a document, or `none` when the text sits outside the
  subset grammar `SPEC.md` states.

  Rules the parser follows:

  - Any `<!` that does not open a comment, and outside content a
    CDATA section, is rejected. That one rule turns away every
    document type declaration and every markup declaration, as the
    subset requires.
  - A reference is one of the five predefined entities or a
    character reference, decimal or hexadecimal, naming a legal
    XML character. Any other reference is rejected: the subset has
    no entities to expand.
  - In an attribute value, a literal tab or line feed reads as a
    space, and a literal carriage return, with or without a line
    feed after it, reads as one space. A character reference is
    never normalized: it reads as the character it names.
  - Character data runs, character references, and CDATA sections
    between two marks are merged into one text run.
  - The XML declaration is rejected: it is a processing
    instruction whose target is the word `xml`, and that target is
    reserved everywhere in this subset.

  Line endings are not normalized in character data, comments,
  processing instruction data, or CDATA sections: a carriage
  return reads as itself. `SPEC.md` states this boundary.

  The functions that can nest or loop (`parseElement`,
  `parseNodes`, `parseAttrs`, `parseCharData`, `parseMisc`,
  `parseTextRun`, `parseAttrValue`) take a fuel count. Each step spends one unit, so the functions are
  total on hostile input. The top level `parse` passes one more
  than the length of the text, which is always enough for a text
  the grammar accepts.
-/

import Xml.Value

namespace Xml

/-- Whitespace in XML: space, tab, line feed, carriage return. -/
def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Drop the whitespace at the head of the text. -/
def skipWs : List Char → List Char
  | [] => []
  | c :: cs => if isWs c then skipWs cs else c :: cs

/-- A digit, as a test. -/
def isDigit (c : Char) : Bool :=
  decide ('0' ≤ c ∧ c ≤ '9')

/-- The value of one hex digit, in either case. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- A hex digit, as a test. -/
def isHexDigit (c : Char) : Bool :=
  (hexVal c).isSome

/-- The longest run of decimal digits at the head of the text, and
    the text after it. -/
def takeDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if isDigit c then
      let (ds, r) := takeDigits rest
      (c :: ds, r)
    else ([], c :: rest)

/-- The longest run of hex digits at the head of the text, and the
    text after it. -/
def takeHexDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if isHexDigit c then
      let (ds, r) := takeHexDigits rest
      (c :: ds, r)
    else ([], c :: rest)

/-- The value of a run of digits in the given base, where `dv`
    gives the value of one digit. An empty run has value zero,
    which the character reference check then rejects, since zero
    names no legal character. -/
def digitsValue (base : Nat) (dv : Char → Nat) (ds : List Char) : Nat :=
  ds.foldl (fun acc d => acc * base + dv d) 0

/-- The character a character reference value names, when the
    value is a legal XML character; otherwise rejection. -/
def charRefChar (n : Nat) : Option Char :=
  if n = 9 ∨ n = 10 ∨ n = 13 ∨ (0x20 ≤ n ∧ n ≤ 0xD7FF) ∨
      (0xE000 ≤ n ∧ n ≤ 0xFFFD) ∨ (0x10000 ≤ n ∧ n ≤ 0x10FFFF)
    then some (Char.ofNat n)
    else none

/-- Read a reference, at the text after the ampersand: one of the
    five predefined entities, or a character reference. Returns
    the character the reference stands for and the text after the
    semicolon. -/
def parseRef : List Char → Option (Char × List Char)
  | 'l' :: 't' :: ';' :: rest => some ('<', rest)
  | 'g' :: 't' :: ';' :: rest => some ('>', rest)
  | 'a' :: 'm' :: 'p' :: ';' :: rest => some ('&', rest)
  | 'a' :: 'p' :: 'o' :: 's' :: ';' :: rest => some ('\'', rest)
  | 'q' :: 'u' :: 'o' :: 't' :: ';' :: rest => some ('"', rest)
  | '#' :: rest =>
    if rest.head? = some 'x' then
      let (ds, r) := takeHexDigits rest.tail
      match r with
      | ';' :: r2 => (charRefChar (digitsValue 16 (fun d => (hexVal d).getD 0) ds)).map
          fun ch => (ch, r2)
      | _ => none
    else
      let (ds, r) := takeDigits rest
      match r with
      | ';' :: r2 => (charRefChar (digitsValue 10 (fun d => d.toNat - 48) ds)).map
          fun ch => (ch, r2)
      | _ => none
  | _ => none

/-- The longest run of name characters at the head of the text,
    and the text after it. -/
def takeNameChars : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if isNameChar c then
      let (ds, r) := takeNameChars rest
      (c :: ds, r)
    else ([], c :: rest)

/-- Read a name at the head of the text: a name start character,
    then name characters. -/
def parseName : List Char → Option (List Char × List Char)
  | c :: rest =>
    if isNameStart c then
      let (ds, r) := takeNameChars rest
      some (c :: ds, r)
    else none
  | [] => none

/-- Read character data up to the next less sign or the end of the
    text: plain characters that are legal XML characters, and
    references. The run `]]>` is rejected, as XML requires. The
    fuel bounds the number of characters and references read,
    since a reference can stand for one character while taking
    several. -/
def parseTextRun : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => some ([], [])
  | fuel + 1, c :: rest =>
    if c = '<' then some ([], c :: rest)
    else if c = '&' then
      match parseRef rest with
      | some (ch, r) => (parseTextRun fuel r).map fun (t, r2) => (ch :: t, r2)
      | none => none
    else if c = ']' then
      if rest.head? = some ']' ∧ (rest.tail).head? = some '>' then none
      else (parseTextRun fuel rest).map fun (t, r) => (c :: t, r)
    else if isLegalChar c then
      (parseTextRun fuel rest).map fun (t, r) => (c :: t, r)
    else none

/-- Read the body of a CDATA section, up to the closing marks. The
    characters are literal: no reference is read, and the run `]]>`
    ends the section wherever it stands. -/
def parseCDATABody : List Char → Option (List Char × List Char)
  | [] => none
  | ']' :: ']' :: '>' :: rest => some ([], rest)
  | c :: rest =>
    if isLegalChar c then
      (parseCDATABody rest).map fun (t, r) => (c :: t, r)
    else none

/-- Read the body of a comment, up to the closing marks. Two
    dashes in a row inside the body are rejected, as XML requires,
    so the first closing marks end the comment. -/
def parseCommentBody : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c = '-' then
      match rest with
      | '-' :: '>' :: r => some ([], r)
      | '-' :: _ => none
      | _ =>
        (parseCommentBody rest).map fun (b, r) => (c :: b, r)
    else if isLegalChar c then
      (parseCommentBody rest).map fun (b, r) => (c :: b, r)
    else none

/-- Read the data of a processing instruction, up to the closing
    marks. The data is literal. -/
def parsePIData : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c = '?' then
      match rest with
      | '>' :: r => some ([], r)
      | _ =>
        (parsePIData rest).map fun (d, r) => (c :: d, r)
    else if isLegalChar c then
      (parsePIData rest).map fun (d, r) => (c :: d, r)
    else none

/-- Read an attribute value, at the text after the opening quote
    `q`. Returns the normalized value and the text after the
    closing quote. A literal less sign is rejected; a literal tab
    or line feed reads as a space; a literal carriage return reads
    as one space, with a line feed right after it read as part of
    the same return. References read as the characters they name,
    with no normalization. The fuel bounds the number of
    characters and references read, as in `parseTextRun`. -/
def parseAttrValue (q : Char) : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, c :: rest =>
    if c = q then some ([], rest)
    else if c = '<' then none
    else if c = '&' then
      match parseRef rest with
      | some (ch, r) => (parseAttrValue q fuel r).map fun (v, r2) => (ch :: v, r2)
      | none => none
    else if c = '\t' ∨ c = '\n' then
      (parseAttrValue q fuel rest).map fun (v, r) => (' ' :: v, r)
    else if c = '\r' then
      match rest with
      | '\n' :: rest2 =>
        (parseAttrValue q fuel rest2).map fun (v, r) => (' ' :: v, r)
      | _ =>
        (parseAttrValue q fuel rest).map fun (v, r) => (' ' :: v, r)
    else if isLegalChar c then
      (parseAttrValue q fuel rest).map fun (v, r) => (c :: v, r)
    else none

/-- Read one processing instruction, at the text after `<?`:
    the target name, then either the closing marks or whitespace
    and the data. The target `xml`, in any case, is rejected: it is
    the XML declaration form, and the reservation holds everywhere
    in this subset. -/
def parsePI (cs : List Char) : Option (Node × List Char) :=
  match parseName cs with
  | some (target, r1) =>
    if target.map Char.toLower = ['x', 'm', 'l'] then none
    else
      match r1 with
      | '?' :: '>' :: r2 => some (.pi target [], r2)
      | c :: _ =>
        if isWs c then
          match parsePIData (skipWs r1) with
          | some (d, r2) => some (.pi target d, r2)
          | none => none
        else none
      | [] => none
  | none => none

/-- Read character data at the head of the text: plain runs,
    references, and CDATA sections, merged into one list of
    characters. Stops before a less sign that does not open a CDATA
    section, and at the end of the text. -/
def parseCharData : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => some ([], [])
  | fuel + 1, '<' :: '!' :: '[' :: 'C' :: 'D' :: 'A' :: 'T' :: 'A' :: '[' :: rest =>
    match parseCDATABody rest with
    | some (t, r) => (parseCharData fuel r).map fun (t2, r2) => (t ++ t2, r2)
    | none => none
  | fuel + 1, '<' :: rest => some ([], '<' :: rest)
  | fuel + 1, cs =>
    match parseTextRun fuel cs with
    | some (t, r) => (parseCharData fuel r).map fun (t2, r2) => (t ++ t2, r2)
    | none => none

/-- Read the attributes of a start tag, and how the tag ends.
    Attributes read so far are in `acc`, in order. Returns the
    attributes, the text after the tag, and whether the tag was
    the empty form. A repeated attribute name is rejected. -/
def parseAttrs : Nat → List (List Char × List Char) → List Char →
    Option (List (List Char × List Char) × List Char × Bool)
  | 0, _, _ => none
  | fuel + 1, acc, cs =>
    match skipWs cs with
    | '/' :: '>' :: rest => some (acc, rest, true)
    | '>' :: rest => some (acc, rest, false)
    | c :: _ =>
      if isNameStart c then
        match parseName (skipWs cs) with
        | some (aname, r1) =>
          match skipWs r1 with
          | '=' :: r2 =>
            match skipWs r2 with
            | '"' :: r3 =>
              match parseAttrValue '"' fuel r3 with
              | some (v, r4) =>
                if acc.any (fun kv => kv.1 = aname) then none
                else parseAttrs fuel (acc ++ [(aname, v)]) r4
              | none => none
            | '\'' :: r3 =>
              match parseAttrValue '\'' fuel r3 with
              | some (v, r4) =>
                if acc.any (fun kv => kv.1 = aname) then none
                else parseAttrs fuel (acc ++ [(aname, v)]) r4
              | none => none
            | _ => none
          | _ => none
        | none => none
      else none
    | [] => none

mutual
/-- Read one element, at the less sign of its start tag. -/
def parseElement : Nat → List Char → Option (Node × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match cs with
    | '<' :: rest =>
      match parseName rest with
      | some (name, r1) =>
        match parseAttrs fuel [] r1 with
        | some (attrs, r2, true) => some (.elem name attrs [], r2)
        | some (attrs, r2, false) =>
          match parseNodes fuel r2 with
          | some (content, r3) =>
            match r3 with
            | '<' :: '/' :: r4 =>
              match parseName r4 with
              | some (ename, r5) =>
                match skipWs r5 with
                | '>' :: r6 =>
                  if ename = name then some (.elem name attrs content, r6)
                  else none
                | _ => none
              | none => none
            | _ => none
          | none => none
        | none => none
      | none => none
    | _ => none

/-- Read the content of an element: nodes up to the end tag, which
    is not consumed. Also returns at the end of the text. -/
def parseNodes : Nat → List Char → Option (List Node × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match cs with
    | [] => some ([], [])
    | '<' :: '/' :: _ => some ([], cs)
    | '<' :: '!' :: '-' :: '-' :: rest =>
      match parseCommentBody rest with
      | some (body, r) =>
        (parseNodes fuel r).map fun (ns, r2) => (.comment body :: ns, r2)
      | none => none
    | '<' :: '!' :: '[' :: 'C' :: 'D' :: 'A' :: 'T' :: 'A' :: '[' :: _ =>
      match parseCharData fuel cs with
      | some (t, r) =>
        if t = [] then parseNodes fuel r
        else (parseNodes fuel r).map fun (ns, r2) => (.text t :: ns, r2)
      | none => none
    | '<' :: '?' :: rest =>
      match parsePI rest with
      | some (n, r) =>
        (parseNodes fuel r).map fun (ns, r2) => (n :: ns, r2)
      | none => none
    | '<' :: c :: _ =>
      if isNameStart c then
        match parseElement fuel cs with
        | some (n, r) =>
          (parseNodes fuel r).map fun (ns, r2) => (n :: ns, r2)
        | none => none
      else none
    | '<' :: [] => none
    | _ =>
      match parseCharData fuel cs with
      | some (t, r) =>
        if t = [] then parseNodes fuel r
        else (parseNodes fuel r).map fun (ns, r2) => (.text t :: ns, r2)
      | none => none
end

/-- Read the miscellany of a prolog or an epilog: comments and
    processing instructions, with whitespace around them. Returns
    the nodes and the text that follows, which starts at the first
    character that is neither whitespace nor a comment or a
    processing instruction. -/
def parseMisc : Nat → List Char → Option (List Node × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    let s := skipWs cs
    match s with
    | '<' :: '!' :: '-' :: '-' :: rest =>
      match parseCommentBody rest with
      | some (body, r) =>
        (parseMisc fuel r).map fun (ns, r2) => (.comment body :: ns, r2)
      | none => none
    | '<' :: '?' :: rest =>
      match parsePI rest with
      | some (n, r) =>
        (parseMisc fuel r).map fun (ns, r2) => (n :: ns, r2)
      | none => none
    | _ => some ([], s)

/-- Parse a whole text: a prolog, one root element, an epilog, and
    nothing else. -/
def parseDocument (fuel : Nat) (cs : List Char) : Option Document :=
  match parseMisc fuel cs with
  | some (prolog, r1) =>
    match parseElement fuel r1 with
    | some (root, r2) =>
      match parseMisc fuel r2 with
      | some (epilog, r3) => if skipWs r3 = [] then some ⟨prolog, root, epilog⟩ else none
      | none => none
    | none => none
  | none => none

/-- Parse a whole text, with the fuel the length of the text
    allows. -/
def parse (cs : List Char) : Option Document :=
  parseDocument (cs.length + 1) cs

end Xml
