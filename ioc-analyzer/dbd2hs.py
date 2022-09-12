#!/usr/bin/env python3

"""
Parses EPICS DBD files, outputs info as a Haskell module.

Usage:
  ./dbd2hs.py [searchpath1 [searchpath2 [...]]]

Practical usage example:
  ./dbd2hs.py ../therapyControl/opIOC/dbd/ >FieldInfo.hs
"""

import sys
import glob
import os
import re
import itertools
from datetime import datetime
from collections import namedtuple, defaultdict

# An EPICS DBD file is a list of Sections. Each Section has some
# arguments and (optionally) some braces {  } containing a list of
# child sections. For instance,
#   recordtype(ai) {
#     field(DTYP,DBF_DEVICE)
#   }
Section = namedtuple("Section",
  ["name",       # e.g. "recordtype" or "field"
  "args",        # e.g. ["acalcout"] or ["NAME", "DBF_STRING"]
  "children"])   # list of nested Sections

def find_child(section, name):
  for c in section.children:
    if c.name == name:
      return c
  return None

TOKEN_REGEX = re.compile(r'\s*(\w+|"(\\.|[^\\"])*"|.)')

def next_newline(s, start):
  try:
    return s.index("\n", start)
  except ValueError as e:
    return len(s)

def tokenize(s):
  i = 0
  while True:
    match = TOKEN_REGEX.match(s, i)
    if not match:
      break
    i = match.end()
    tok = match.group(1)
    if tok[0] == '"':
      tok = tok[1:-1]
    if tok == '#' or tok == '%': # hash is comments, percent is escape-to-C
      i = next_newline(s, i)
      continue
    # print("consumed {}".format(tok))
    yield tok
  yield None
  assert not s[i:].strip()

class peekable(object):
    def __init__(self, i):
      self.i = i
      self.peeked = False
      self.peek_val = None
    def __iter__(self):
      return self
    def __next__(self):
      if self.peeked:
        self.peeked = False
        v = self.peek_val
        self.peek_val = None
        return v
      return self.i.__next__()
    def next(self):
      return self.__next__()
    def peek(self):
      if self.peeked:
        return self.peek_val
      v = self.i.__next__()
      self.peeked = True
      self.peek_val = v
      return v

def parse_args(tokens):
  assert tokens.next() == "("
  while tokens.peek() != ")":
    yield tokens.next()
    if tokens.peek() == ",":
      tokens.next()
  assert tokens.next() == ")"

def parse_sections(tokens):
  while tokens.peek() is not None and tokens.peek() != "}":
    name = tokens.next()

    if name == "breaktable": # parsing not supported
      while tokens.peek() != "}":
        tokens.next()
      tokens.next()
      continue

    if name == "include":
      f = tokens.next()
      yield Section(name, f, ())
      continue

    args = list(parse_args(tokens))
    if tokens.peek() == "{":
      tokens.next()
      children = list(parse_sections(tokens))
      assert tokens.next() == "}"
    else:
      children = ()

    yield Section(name, args, children)

def run():
  dbdfiles = dict() # maps basename (e.g. "dbCommon.dbd") to absolute paths
  record_types = set() # prevents duplicate outputs
  unhandled = set() # prevents too much output

  filenames = []
  for d in sys.argv[1:]:
    for f in glob.glob("{}/*.dbd".format(d)):
      f = os.path.abspath(f)
      dbdfiles[os.path.basename(f)] = f
      filenames.append(f)

  print("-- THIS FILE WAS AUTOGENERATED ON {} BY: {}".format(datetime.now(), " ".join(sys.argv)))
  print("{-# LANGUAGE Safe #-}")
  print("module FieldInfo where")
  print("import qualified Data.Map as M")

  print("""data FieldType =
    STRING Integer |
    MENU [String] |
    INLINK |
    NOACCESS |
    UCHAR |
    FWDLINK |
    DOUBLE |
    ENUM |
    DEVICE |
    FLOAT |
    CHAR |
    USHORT |
    ULONG |
    LONG |
    OUTLINK |
    SHORT deriving (Eq, Ord, Show)""")

  print("fieldtypes :: M.Map String (M.Map String FieldType)")
  print("fieldtypes = M.fromList [")

  menus = defaultdict(list)
  first_record_type = True
  for filename in filenames:
    with open(filename, "r") as f:
      for section in parse_sections(peekable(tokenize(f.read()))):

        if section.name == "menu":
          menu_name = section.args[0]
          for child in section.children:
            if child.name == "choice":
              menus[menu_name].append(child.args[1])

        elif section.name == "recordtype":
          record_type = section.args[0]
          if record_type in record_types:
            print("skipping duplicate {} in {}".format(record_type, filename), file=sys.stderr)
            continue
          record_types.add(record_type)
          if not first_record_type:
            print("  ,")
          first_record_type = False
          print('  ("{}", M.fromList ['.format(record_type))
          first_field = True
          for child in section.children:
            if child.name == "field":
              if not first_field:
                print(",")
              first_field = False
              field_name, field_type = child.args
              field_type = field_type[4:] # cut off "DBF_"
              if field_type == "MENU":
                options = menus[find_child(child, "menu").args[0]]
                field_type += " [" + ", ".join('"{}"'.format(o) for o in options) + "]"
              elif field_type == "STRING":
                size = find_child(child, "size").args[0]
                field_type += " " + size
              print('    ("{}", {})'.format(field_name, field_type), end="")
          print("  ])")

        elif section.name not in unhandled:
          unhandled.add(section.name)
          print("unhandled section '{}'".format(section.name), file=sys.stderr)

  print("  ]")

if __name__ == "__main__":
  run()
