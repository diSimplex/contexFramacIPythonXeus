project('xeus-calc', 'c', 'cpp')

buildTests = get_option('tests')

subdir('libxcalc')

if buildTests
  message('Building TESTS')
  subdir('tests')
else
  message('Building xcalc')
  subdir('xcalc')
  subdir('share' / 'jupyter' / 'kernels' / 'xcalc')
endif
