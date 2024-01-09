#!/bin/bash

if [[ "$#" -ne 1 ]]; then
    echo -e "USAGE\n"
    echo -e "$0 COPYRIGHT_YEAR_RANGE"
fi

find hdl -type f -print0 | xargs -0 sed -i "s/Copyright (C) [0-9\-]\+,/Copyright (C) $1,/g"
