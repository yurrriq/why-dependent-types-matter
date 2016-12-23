docs/idris.html: idris/Data/YDTM.lidr
	pandoc \
	-f markdown_github+lhs+tex_math_dollars -t html \
	-s -o $@ \
	$<

docs/idris.md: idris/Data/YDTM.lidr
	pandoc \
	-f markdown_github+lhs+tex_math_dollars -t markdown_github \
	-s -o $@ \
	$<
