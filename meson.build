project('xeus-calc', 'c', 'cpp')

buildTests = get_option('tests')

if buildTests
  subdir('tests')
  subdir('src')
else
  subdir('src')
  subdir('xeus')
  subdir('share' / 'jupyter' / 'kernels' / 'xcalc')
endif
