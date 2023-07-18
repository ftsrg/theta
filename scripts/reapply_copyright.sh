#!/bin/bash
scriptdir=$(dirname $(realpath "$0"))

for file in $(find $scriptdir/../ -type f \( -name "*.java" -o -name "*.kt" -o -name "*.kts" \)); do
    last_modified_year=$(cd "$(dirname $file)" && git log -1 --format=%ad --date=format:%Y "$(basename $file)")

    header_exists=$(head -n 2 "$file" | tail -n 1 | grep -c "Budapest University of Technology")

    if [[ $header_exists -eq 0 ]]; then
        echo "Adding copyright header to $file"
        cat ./doc/copyright-header.txt "$file" > tmp_026204264
        mv tmp_026204264 "$file"
    fi

    header_year=$(head -n 2 "$file" | tail -n 1 | grep -o -E '[0-9]{4}')

    if [[ "$header_year" != "$last_modified_year" ]]; then
        echo "Updating copyright year to $last_modified_year in $file (was $header_year)"
        sed -i "s/Copyright [0-9]\{4\}/Copyright $last_modified_year/g" "$file"
    fi
done
