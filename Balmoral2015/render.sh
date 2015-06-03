#!/bin/sh
# --self-contained
HTML_ARGS="-w dzslides --standalone --filter panpipe --filter panhandle"

function go {
    echo "Rendering $1"
    rm "$1.html" 2> /dev/null
    PATTERN="$1\.md" EXTENSION=html ARGS="$HTML_ARGS" md2pdf
}

go "dependent_type_problems"
go "constructive"
go "machine_learning_intro"
go "machine_learning_languages"

echo "Done"
