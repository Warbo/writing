# Build slides.md with Beamer
function slides {
  PATTERN="slides\.md" EXTENSION=html ARGS="-w dzslides --standalone --self-contained --filter pandoc-citeproc" md2pdf
}

# Build abstract.md
function abstract {
  PATTERN="abstract\.md" ARGS="--template=./templates/default.latex -N" OPTIONS=pp md2pdf
}

pids=()
trap 'kill "${pids[@]}"' EXIT
slides &
pids+=("$!")
abstract &
pids+=("$!")

echo "Waiting for ${pids[@]}"
wait
