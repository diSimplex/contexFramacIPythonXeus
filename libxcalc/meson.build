
deps = declare_dependency(
	include_directories: [ '..'/'include'],
)

libxcalc = library(
	'libxcalc',
	'token.c',
	#'calc.c',
	dependencies: deps,
	install: true
)
