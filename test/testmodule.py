def f1():
  print("Called f1")

def f2(str1, str2bytes, **kwargs):
  print("Called f2:", (str1, str2bytes, kwargs))
  return 1
