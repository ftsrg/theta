#!/bin/bash

file1="$1"
file2="$2"

# Step 1: Preprocess files to normalize whitespace (remove extra spaces and tabs)
normalize_whitespace() {
    local file="$1"
    sed 's/[[:space:]]\+/ /g; s/^[[:space:]]*//; s/[[:space:]]*$//' "$file"
}

# Step 2: Use `wdiff` to get unmodified words from both files after normalizing whitespace
get_unmodified_words() {
    local norm_file1="$1"
    local norm_file2="$2"
    wdiff -n <(indent -st "$norm_file1") <(indent -st "$norm_file2") \
    | grep -oE '[^ \{\[\+\-][^ \{\[\+\-]*' | tr -d '[:space:]'  # Extract words not marked as changed (without WS)
}

# Step 2: Tokenize a C file based on statements, using only unmodified words
tokenize_c_file() {
    local file="$1"
    local line_num=1
    local offset=0
    local buffer=""
    
    # Read the file line by line
    while IFS= read -r line; do
        # Add the current line to the buffer (preserve indentation and spacing)
        buffer="$buffer $line"
        
        # Tokenize based on semicolons, braces, and common control structures
        while [[ "$buffer" =~ ^(.*?)([;{}])(.*)$ ]]; do
            statement="${BASH_REMATCH[1]}${BASH_REMATCH[2]}"
            rest="${BASH_REMATCH[3]}"
            
            # Trim leading/trailing spaces from statement
            statement=$(echo "$statement" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')

            # Check if the statement contains only unmodified words
            if [ -n "$statement" ]; then
                tmp=${buffer%%$statement*}
                tmp=$(echo "$tmp" | tail -n1)
                column_num=${#tmp}
                echo "$statement;SEP;$line_num;SEP;$column_num;SEP;$offset"
                offset=$((offset + ${#statement}))
            fi

            # Continue with the rest of the buffer
            buffer="$rest"
        done
        
        # Track the total offset and line numbers
        line_num=$((line_num + 1))
        offset=$((offset + ${#line} + 1))
    done < "$file"
}

# Step 4: Tokenize both files
file1_tokens=$(mktemp)
file2_tokens=$(mktemp)
tokenize_c_file "$file1" > "$file1_tokens"
tokenize_c_file "$file2" > "$file2_tokens"

# Step 5: Set up variables to keep track of token positions
file1_word_count=$(wc -l < "$file1_tokens")
file2_word_count=$(wc -l < "$file2_tokens")

# Step 6: Compare tokens (C statements) from both files in lockstep, advancing file2 as needed
file1_pos=1
file2_pos=1

echo "statements:"

while [ "$file1_pos" -le "$file1_word_count" ] && [ "$file2_pos" -le "$file2_word_count" ]; do
    # Read the current token (C statement) from file1
    file1_statement=$(sed -n "${file1_pos}p" "$file1_tokens" | awk -F ';SEP;' '{print $1}')
    file1_line_num=$(sed -n "${file1_pos}p" "$file1_tokens" | awk -F ';SEP;' '{print $2}')
    file1_col_num=$(sed -n "${file1_pos}p" "$file1_tokens" | awk -F ';SEP;' '{print $3}')
    file1_offset=$(sed -n "${file1_pos}p" "$file1_tokens" | awk -F ';SEP;' '{print $4}')

    # Read the current token (C statement) from file2
    file2_statement=$(sed -n "${file2_pos}p" "$file2_tokens" | awk -F ';SEP;' '{print $1}')
    file2_line_num=$(sed -n "${file2_pos}p" "$file2_tokens" | awk -F ';SEP;' '{print $2}')
    file2_col_num=$(sed -n "${file2_pos}p" "$file2_tokens" | awk -F ';SEP;' '{print $3}')
    file2_offset=$(sed -n "${file2_pos}p" "$file2_tokens" | awk -F ';SEP;' '{print $4}')

    # Compare file1 and file2 tokens (C statements)
    if [ "$(echo "$file1_statement" | tr -d '[:space:]')" = "$(echo "$file2_statement" | tr -d '[:space:]')" ]; then
        echo "  - text: '$file1_statement'"
        echo "    file1:"
        echo "      line: $file1_line_num"
        echo "      col: $file1_col_num"
        echo "      offset: $file1_offset"
        echo "    file2:"
        echo "      line: $file2_line_num"
        echo "      col: $file2_col_num"
        echo "      offset: $file2_offset"
        echo

        # Move to the next statement in both files
        file1_pos=$((file1_pos + 1))
        file2_pos=$((file2_pos + 1))
    else
        # If no match, advance file2 to find a match
        file2_pos=$((file2_pos + 1))
        if [ "$file2_pos" -gt "$file2_word_count" ]; then
            file1_pos=$((file1_pos + 1))
            file2_pos=1  # Reset file2 to the beginning for the next file1 statement
        fi
    fi
done

# Clean up temporary files
rm "$file1_tokens" "$file2_tokens"
