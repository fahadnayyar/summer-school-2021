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
solutions_dir = os.path.relpath(os.path.join(instructor_dir, "../summer-school-2021-solutions/"))
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
    return "elide" not in self.filename and self.type not in ["hints", "demos"]

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

  def solution_path(self):
    return os.path.join(solutions_dir, self.exercise_rel_path)

  def exercise_path(self):
    return os.path.join(student_dir, self.exercise_rel_path)

  def path_for_inline(self, line):
    mo = re.compile('\S+\s+"(\S+)"').search(line)
    assert mo
    return mo.groups()[0]

  def inline(self, including_path, line, duplicate_detector):
    inlinefile = self.path_for_inline(line)
    if inlinefile in duplicate_detector:
      #print(f"  rejecting duplicate {inlinefile}")
      return []
    inlinepath = os.path.join(os.path.dirname(including_path), inlinefile)
    #print(f" inline file {inlinefile} from {including_path} with dupset {duplicate_detector}")
    lines = [line.rstrip() for line in open(inlinepath).readlines()]
    output_lines = []
    for line in lines:
      if (line.startswith("include")
          # what a hackaroo
          and not "library" in line):
          #and not "elide" in line):
        #print("thinking about ", inlinefile)
        #print(f"  inlining from {inlinefile}, dupset now {duplicate_detector}")
        output_lines += self.inline(inlinepath, line, duplicate_detector)
        duplicate_detector.add(inlinefile)
      elif line.startswith("//#"):
        pass
      else:
        output_lines.append(line)
    return output_lines

  def transform_solution_to_exercise(self):
    #print(f"chapter {self.chapter} filename {self.filename}")
    duplicate_detector = set()
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
      elif input_line.startswith("//#excludefrominline"):
        exclude = input_line.split()[-1]
        #print(f"- excludefrominline {exclude}")
        duplicate_detector.add(exclude)
        output_line = None
      elif "//#magicinline" in input_line:
        #print("  yo bro", input_line, "dd", duplicate_detector)
        output_lines += self.inline(self.instructor_path(), input_line, duplicate_detector)
        output_line = None
      elif "//#magicinclude" in input_line:
        output_line = self.fixup_solution_include(input_line)
      elif input_line.startswith("//#inline"):
        output_lines += self.inline(self.instructor_path(), input_line, duplicate_detector)
        output_line = None
      elif elide:
        output_line = None
      if output_line!=None:
        output_lines.append(output_line)
    mkdirs(self.exercise_path())
    open(self.exercise_path(), "w").write(''.join([line+"\n" for line in output_lines]))
    #print(f"Generated {self.exercise_path()}")

  def fixup_solution_include(self, include_line):
    include_path = re.compile('include "(.*)"').search(include_line).groups()[0]
    new_path = include_path.replace("/solutions/", "/exercises/").replace("_solution.", ".")
    return f'include "{new_path}"'

  # haaaaack party
  def transform_solution_to_published_solution(self):
    #print(f"solns-chapter {self.chapter} filename {self.filename}")
    duplicate_detector = set()
    input_lines = [line.rstrip() for line in open(self.instructor_path()).readlines()]
    output_lines = []
    for input_line in input_lines:
      output_line = input_line
      if (input_line.startswith("//#exercise")
        or input_line.startswith("//#inline")
        or input_line.startswith("//#start-elide")
        or input_line.startswith("//#end-elide")
        or input_line.startswith("//#extratopsecrethackmarkforelision")
        ):
        continue
      elif input_line.startswith("//#excludefrominline"):
        exclude = input_line.split()[-1]
        #print(f"- excludefrominline {exclude}")
        duplicate_detector.add(exclude)
      elif "//#magicinline" in input_line:
        #print("  yo bro", input_line)
        output_lines += self.inline(self.instructor_path(), input_line, duplicate_detector)
        output_line = None
      elif "//#magicinclude" in input_line:
        output_line = self.fixup_solution_include(input_line)
      if output_line!=None:
        output_lines.append(output_line)
    mkdirs(self.solution_path())
    open(self.solution_path(), "w").write(''.join([line+"\n" for line in output_lines]))

  def compile(self):
    #print(f"-- {self.type}/{self.filename}")
    if self.type == "solutions":
      # solutions map into exercises dir
      #print(f"Transform {self.num}")
      if "elide" not in self.filename:
        self.transform_solution_to_exercise()
        self.transform_solution_to_published_solution()
    else:
      # everything else goes in the same relative dir
      mkdir_and_copy(self.instructor_path(), self.student_path())

  def test_dafny(self, pathfn, verify):
    if not self.is_dafny_source():
      return []
    if "impl_model_for_ex04" in self.filename:
      # Hacky special case: This file is only meant to be included in a
      # particular way by others, and has no interesting content, and due
      # to wacky inline/include rules, it doesn't have access to the
      # CommitTypes module until it's included elsewhere. So skip it.
      return []
    path = pathfn()
    verifyFlag = ["/noVerify"] if not verify else []
    cmd = ["dafny"] + verifyFlag + ["/compile:0", "/vcsCores:6", "/timeLimit:10", path]
    print(f"  -- {' '.join(cmd)}")
    return [(self, subprocess.call(cmd)==0)]
#    if "midterm" in path: #XXX TODO skipping to final
#        return [(self, subprocess.call(cmd)==0)]
#    else:
#        return [(self, True)]

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
    for path in glob.glob(instructor_dir+"/chapter*/*/*") + glob.glob(instructor_dir+"/*-project/*/*"):
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

  def blast_dir(self, dirname):
      try:
        shutil.rmtree(dirname)
      except FileNotFoundError: pass
      os.mkdir(dirname)

  def clean_output(self):
    # Destroy existing data
    for chapter in sorted(self.elements.keys()):
      self.blast_dir(os.path.join(student_dir, chapter))
      self.blast_dir(os.path.join(solutions_dir, chapter))

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
        if "elide" in element.filename:
          continue
        fp.write(element.md_catalog_row())

  def test_elements(self):
    results = []
    verify = True
    def test_elt(elt, results):
      results+=elt.test_dafny(elt.instructor_path, verify)
      results+=elt.test_dafny(elt.solution_path, verify)
      # don't bother verifying student-view of exercises
      results+=elt.test_dafny(elt.exercise_path, False)
    self.foreach_element(lambda elt: test_elt(elt, results))
    failures = []
    for (elt, result) in results:
      if result==False:
        failures.append(elt)
    if len(failures)==0:
      print(f"All {len(results)} tests passed")
    else:
      print(f"Failing tests count: {len(failures)}")
      print(failures)

  def copy_library(self):
    for in_path in glob.glob(instructor_dir+"/library/*"):
      suffix = in_path[len(instructor_dir)+1:]
      mkdir_and_copy(in_path, os.path.join(student_dir, suffix))
      mkdir_and_copy(in_path, os.path.join(solutions_dir, suffix))

  def compile(self):
    self.compile_elements()
    self.build_catalog()
    self.copy_library()

def main():
  catalog = Catalog()
  action = sys.argv[1] if len(sys.argv)==2 else "compile"
  if action=="compile":
    catalog.compile()
  elif action=="test":
    catalog.compile()
    Catalog().test_elements()
  else:
    print("Invalid verb.")
    sys.exit(-1)

main()
