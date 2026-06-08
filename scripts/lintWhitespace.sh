#!/usr/bin/env bash

tmpfile=$(mktemp)
issues_found=0

validate_spaces () {
    find ArkLib -type f -name "*.lean" | while IFS= read -r file; do
        # Check for trailing whitespace and print line number if found
        while IFS=: read -r line_num line; do
            echo "Trailing whitespace found in $file at line $line_num: $line"
            echo 1 > "$tmpfile"
        done < <(grep -n "[[:blank:]]$" "$file")

        # Check if the last line ends with a new line
        if [ "$(tail -c 1 "$file" | od -c | awk 'NR==1 {print $2}')" != "\n" ]; then
            echo "Last line does not end with a new line in: $file"
            echo 1 > "$tmpfile"
        fi
    done

    if [ -f "$tmpfile" ]; then
        issues_found=$(<"$tmpfile")
    fi
    rm -f "$tmpfile"

    if [ $issues_found ]; then
        echo "Run \`bash ./scripts/lintWhitespace.sh -i\` to fix whitespace issues."; 
    fi

    exit $issues_found
}

fix_spaces_inplace() {
    for file in $(find ArkLib -type f -name "*.lean")
    do 
        # Remove trailing `\t` and ` `.
        sed -i 's/[ \t]*$//' "$file"
        # Add trailing '\n' to the file
        sed -i -e '$a\' "$file"
    done
}

is_inplace=0

while getopts ":i" option; do
  case $option in
    i)
      is_inplace=1 ;;
    *)
      echo "Usage: $0 [-i]" 
      exit 1
      ;;
  esac
done

if [ $is_inplace -eq 1 ]; then fix_spaces_inplace; else validate_spaces; fi
    


