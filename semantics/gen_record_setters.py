import sys
import re

DECL_PART_RE = re.compile(r'\s*(([a-zA-Z0-9_]+)|[({]([a-zA-Z0-9_ ]+):[a-zA-Z0-9_ ]+[)}])')

def collect_parts(line):
    i = 0
    while True:
        m = DECL_PART_RE.match(line, i)
        if not m:
            break
        i = m.end()

        name_str = m.group(2) or m.group(3)
        names = [n.strip() for n in name_str.split()]
        for n in names:
            if n != '':
                yield n


def main(input_path, output_path, module):
    in_file = open(input_path)
    out_file = open(output_path, 'w')
    inline = module == ''

    it = iter(in_file)
    def take():
        try:
            line = next(it)
            if inline:
                out_file.write(line)
            return line
        except StopIteration:
            return None

    records = []

    while True:
        l = take()
        if l is None:
            break

        if l.startswith('Record '):
            parts = list(collect_parts(l))
            print(repr(l), parts)
            ty = parts[1]
            params = parts[2:]

            first = take()
            ctor = first.strip().split()[0]
            fields = []

            need_semi = False
            while True:
                cur = take()

                if cur.strip().startswith('}'):
                    break

                if need_semi:
                    if cur.rstrip().endswith(';'):
                        need_semi = False
                    continue

                parts = cur.strip().split()
                if parts[1] != ':':
                    continue
                field = parts[0]
                fields.append(field)
                if not parts[-1].endswith(';'):
                    need_semi = True

            records.append((ty, ctor, params, fields))

    from pprint import pprint
    pprint(records)

    if not inline:
        out_file.write('Require Import %s.\n' % module)

    for (ty, ctor, params, fields) in records:
        count = len(fields)
        param_str = ' '.join('{%s}' % p for p in params)
        ty_str = '%s %s' % (ty, ' '.join(params))
        for i, name in enumerate(fields):
            wilds = ' '.join('_' for _ in params)
            pats = ' '.join('x%d' % j for j in range(count))
            pats_ = ' '.join('x%d%s' % (j, "'" if j == i else '') for j in range(count))
            out_file.write("\nDefinition set_%s %s (r : %s) x%d' : %s :=\n" %
                    (name, param_str, ty_str, i, ty_str))
            out_file.write("    let '(%s %s %s) := r in\n" % (ctor, wilds, pats))
            out_file.write("    %s %s %s.\n" % (ctor, wilds, pats_))

if __name__ == '__main__':
    input_path, output_path, module = sys.argv[1:]
    main(input_path, output_path, module)
