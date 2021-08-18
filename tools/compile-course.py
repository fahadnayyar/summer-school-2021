#!/usr/bin/python3

import collections
import glob
import os
import re
import shutil
import operator
import subprocess
import sys

script_dir = os.path.dirname(__file__)
instructor_dir = os.path.relpath(os.path.join(script_dir, ".."))
#print(f"instructor_dir  {instructor_dir}")
student_dir = os.path.relpath(os.path.join(instructor_dir, "../summer-school-2021/"))
#print(f"student_dir  {student_dir}")

def mkdirs(dstpath):
  """Make directories to include file dstpath, if necessary"""
  try:
    os.makedirs(os.path.dirname(dstpath))
  except FileExistsError: pass

def mkdir_and_copy(srcpath, dstpath):
  """Copy file from srcpath to dstpath, creating any necessary directories."""
  mkdirs(dstpath)
  shutil.copyfile(srcpath, dstpath)

class Element:
  def __init__(self, chapter, type, filename):
    self.chapter = chapter
    self.type = type
    self.filename = filename
    self.extra_top_secret_inline_elision_paths = set()

    self.num = None
    if type=="solutions":
      mo = re.compile("exercise(\d+)_solution.dfy").search(filename)
      if mo:
        self.num = mo.groups()[0]
      self.exercise_rel_path = os.path.join(self.chapter, "exercises",
        f"exercise{self.num}.dfy" if self.num else self.filename)
    else:
      self.exercise_rel_path = None

  def is_dafny_source(self):
    return self.num != None

  def key(self):
    return (self.chapter, self.type, self.filename)

  def __repr__(self):
    return self.instructor_path()

  def __lt__(self, other):
    return operator.lt(self.key(), other.key())

  def instructor_path(self):
    return os.path.join(instructor_dir, self.chapter, self.type, self.filename)

  def student_path(self):
    return os.path.join(student_dir, self.chapter, self.type, self.filename)

  def exercise_path(self):
    return os.path.join(student_dir, self.exercise_rel_path)

  def path_for_inline(self, line):
    mo = re.compile('\S+\s+"(\S+)"').search(line)
    assert mo
    return mo.groups()[0]

  def inline(self, including_path, line):
    inlinefile = self.path_for_inline(line)
    inlinepath = os.path.join(os.path.dirname(including_path), inlinefile)
    lines = [line.rstrip() for line in open(inlinepath).readlines()]
    output_lines = []
    for line in lines:
      if (line.startswith("include")
          # what a hackaroo
          and not "library" in line):
          #and not "elide" in line):
        print("thinking about ", self.path_for_inline(line))
        if (self.path_for_inline(line) in self.extra_top_secret_inline_elision_paths):
          print("top-secret-eliding f{self.path_for_inline(line)}")
        else:
            output_lines += self.inline(inlinepath, line)
      elif line.startswith("//#"):
        pass
      else:
        output_lines.append(line)
    return output_lines

  def transform_solution(self):
    print(f"filename {self.filename}")
    if "elide" in self.filename:
      return
    elide = False
    input_lines = [line.rstrip() for line in open(self.instructor_path()).readlines()]
    output_lines = []
    for input_line in input_lines:
      output_line = input_line
      if input_line.startswith("//#exercise"):
        # exercise substitution
        output_line = input_line[11:]
      elif input_line.startswith("//#elide"):
        # single-line elision
        output_line = None
      elif input_line.startswith("//#start-elide"):
        # multi-line elision
        assert not elide    # mismatched start-end elide
        elide = True
        output_line = None
      elif input_line.startswith("//#end-elide"):
        assert elide    # mismatched start-end elide
        elide = False
        output_line = None
      elif input_line.startswith("//#extratopsecrethackmarkforelision"):
        # I'm so ashamed.
        self.extra_top_secret_inline_elision_paths.add(input_line.split(" ")[-1].strip('"'))
      elif input_line.startswith("//#inline"):
        output_lines += self.inline(self.instructor_path(), input_line)
        elide = False
        output_line = None
      elif elide:
        output_line = None
      if output_line!=None:
        output_lines.append(output_line)
    mkdirs(self.exercise_path())
    open(self.exercise_path(), "w").write(''.join([line+"\n" for line in output_lines]))
    #print(f"Generated {self.exercise_path()}")

  def compile(self):
    #print(f"-- {self.type}/{self.filename}")
    if self.type == "solutions":
      # solutions map into exercises dir
      #print(f"Transform {self.num}")
      self.transform_solution()
    else:
      # everything else goes in the same relative dir
      mkdir_and_copy(self.instructor_path(), self.student_path())

  def test(self):
    if self.is_dafny_source():
      cmd = ["dafny", "/compile:0", "/vcsCores:6", self.instructor_path()]
      print(f"  -- {' '.join(cmd)}")
      return subprocess.call(cmd)==0

  def extract_docs(self):
    input_lines = [line.rstrip() for line in open(self.instructor_path()).readlines()]
    self.title = " ".join([l.replace("//#title", "").strip()
            for l in input_lines if l.startswith("//#title")])
    self.description = " ".join([l.replace("//#desc", "").strip()
            for l in input_lines if l.startswith("//#desc")])

  def md_catalog_row(self):
    if not(self.exercise_rel_path) or "elide" in self.exercise_rel_path:
      return ""
    row = f"- [`{self.exercise_rel_path}`]({self.exercise_rel_path})"
    if self.title:
      row += f"<br>**{self.title}**"
    if self.description:
      row += f" -- {self.description}"
    row += "\n\n"
    return row

class Catalog:
  def __init__(self):
    self.gather_elements()

  def gather_elements(self):
    self.elements = collections.defaultdict(lambda: collections.defaultdict(set))
    for path in glob.glob(instructor_dir+"/chapter*/*/*"):
      suffix = path[len(instructor_dir)+1:]
      element = Element(*suffix.split("/"))
      self.elements[element.chapter][element.type].add(element)

  def foreach_element(self, fun):
    for chapter in sorted(self.elements.keys()):
      for type in sorted(self.elements[chapter].keys()):
        for element in sorted(self.elements[chapter][type]):
          try:
            fun(element)
          except:
            print(f"While processing {element}:")
            raise

  def clean_output(self):
    # Destroy existing data
    for chapter in sorted(self.elements.keys()):
      output_chapter = os.path.join(student_dir, chapter)
      try:
        shutil.rmtree(output_chapter)
      except FileNotFoundError: pass
      os.mkdir(output_chapter)

  def get_elements(self):
    element_list = []
    self.foreach_element(lambda elt: element_list.append(elt))
    return element_list

  def compile_elements(self):
    self.clean_output()
    self.foreach_element(lambda elt: elt.compile())

  def build_catalog(self):
    self.foreach_element(lambda elt: elt.extract_docs())

    chapter = None
    catalog_filename = os.path.join(student_dir, "exercises.md")
    with open(catalog_filename, "w") as fp:
      fp.write("# Index of exercises\n\n")
      for element in self.get_elements():
        if element.chapter != chapter:
          chapter = element.chapter
          fp.write(f"## {chapter}\n\n")
        fp.write(element.md_catalog_row())

  def test_elements(self):
    results = []
    self.foreach_element(lambda elt: results.append((elt, elt.test())))
    failures = []
    for (elt, result) in results:
      if result==False:
        failures.append(elt)
    if len(failures)==0:
      print("All tests passed")
    else:
      print(f"Failing tests count: {len(failures)}")
      print(failures)

  def copy_library(self):
    for in_path in glob.glob(instructor_dir+"/library/*"):
      suffix = in_path[len(instructor_dir)+1:]
      out_path = os.path.join(student_dir, suffix)
      shutil.copyfile(in_path, out_path)

def main():
  action = sys.argv[1] if len(sys.argv)==2 else "compile"
  if action=="compile":
    Catalog().compile_elements()
    Catalog().build_catalog()
    Catalog().copy_library()
  elif action=="test":
    Catalog().test_elements()
  else:
    print("Invalid verb.")
    sys.exit(-1)

main()
