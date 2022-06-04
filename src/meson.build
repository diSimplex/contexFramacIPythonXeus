cppComp = meson.get_compiler('cpp')

prefix    = get_option('prefix')
prefixInc = prefix / 'include'
prefixLib = prefix / 'lib'

conda = declare_dependency(
	include_directories: [ '..'/ 'include', prefixInc ],
)

deps = [
  cppComp.find_library('libxeus', dirs: prefixLib),
  cppComp.find_library('libzmq', dirs: prefixLib),
  conda
]

libxcalc = library(
	'libxeus-calc',
	'xeus_calc_interpreter.cpp',
	dependencies: deps,
	install: true
)

executable(
  'xcalc',
  'main.cpp',
  link_with: libxcalc,
  dependencies: deps,
  install: true,
)