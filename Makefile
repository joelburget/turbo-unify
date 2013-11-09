unify.jsexe: unify.hs index.html
	ghcjs unify.hs -o unify; \
	cp index.html unify.jsexe/
