# Detect blanket package-root imports in Lean module headers.
#
# Accepted header modifiers are tokenized rather than matched as one spelling, so this covers
# legacy imports, module-system visibility/meta modifiers, `import all`, and import commands that
# name more than one module. Owner modules such as `VCVio.OracleComp.OracleSpec` do not match.

BEGIN {
  forbidden["ArkLib"] = 1
  forbidden["Mathlib"] = 1
  forbidden["VCVio"] = 1
  forbidden["CompPoly"] = 1
  forbidden["PolyFun"] = 1
  forbidden["Batteries"] = 1
  found = 0
}

{
  source = $0
  line = $0
  sub(/[[:space:]]*--.*/, "", line)
  sub(/^[[:space:]]*/, "", line)
  sub(/[[:space:]]*$/, "", line)
  if (line == "")
    next

  count = split(line, token, /[[:space:]]+/)
  pos = 1

  if (token[pos] == "public" || token[pos] == "private")
    pos++
  if (token[pos] == "meta")
    pos++
  if (token[pos] != "import")
    next
  pos++
  if (token[pos] == "all")
    pos++

  for (; pos <= count; pos++) {
    if (token[pos] in forbidden) {
      print FILENAME ":" FNR ":" source
      found = 1
      break
    }
  }
}

END {
  exit found
}
