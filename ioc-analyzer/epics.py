#!/usr/bin/env python3

class Database(object):
    def __init__(self):
        self.db = {}

    def register(self, name, record):
        assert name not in self.db
        record.db = self
        self.db[name] = record

    def get(self, name):
        return self.db.get(name)

class Link(object):
    def __init__(self, owner, name, field, pp_get=False, pp_set=False):
        self.owner = owner
        self.name = name
        self.field = field
        self.record = None
        self.pp_get = pp_get
        self.pp_set = pp_set

    def resolve(self):
        self.record = self.owner.db.get(self.name)

    def get(self):
        if self.record is None:
            self.resolve()

        if self.pp_get and self.record.passive:
            self.record.process()
        return getattr(self.record, self.field)

    def set(self, value):
        if self.record is None:
            self.resolve()

        setattr(self.record, self.field, value)

        if self.pp_set and self.record.passive:
            self.record.process()

    def process(self):
        if self.record is None:
            self.resolve()

        if self.record.passive:
            self.record.process()

class ConstLink(object):
    def __init__(self, value):
        self.value = value

    def resolve(self):
        pass

    def get(self):
        return self.value

    def set(self, value):
        raise NotImplemented

    def process(self):
        raise NotImplemented

def make_link(link_str, owner):
    if link_str is None:
        return None

    try:
        value = float(link_str)
        return ConstLink(value)
    except ValueError:
        pass

    parts = link_str.split()

    name, dot, field = parts[0].rpartition('.')
    flags = parts[1:]

    if not dot:
        name = field
        field = 'result'
    field = field.lower()

    # "PP" = "process passive": If the target record has 'SCAN = Passive', then
    # process that record before each read.
    # "CA" = "channel access": If the target record has 'SCAN = Passive', then
    # a Channel Access put will trigger processing after writing.
    return Link(owner, name, field, pp_get=('PP' in flags), pp_set=('CA' in flags))

class Record(object):
    def __init__(self, **kwargs):
        self.db = None
        self.passive = kwargs.get('scan', 'Passive') == 'Passive'
        self.forward_link = make_link(kwargs.get('flnk'), self)

    def __setattr__(self, k, v):
        if k == 'proc':
            self.process()
        else:
            super(Record, self).__setattr__(k, v)

    def process(self):
        self.process_impl()

        if self.forward_link is not None:
            self.forward_link.process()

    def process_impl(self):
        pass

class DummyRecord(Record):
    def __getattr__(self, k):
        return 0

    def __setattr__(self, k, v):
        pass

class Calc(Record):
    def __init__(self, **kwargs):
        super(Calc, self).__init__(**kwargs)

        self.inputs = [0] * 12
        self.in_links = [None] * 12
        self.result = 0
        self.formula = kwargs['calc']

        for i in range(12):
            field = 'inp' + chr(i + ord('a'))
            if field in kwargs:
                self.in_links[i] = make_link(kwargs[field], self)

            field = chr(i + ord('a'))
            if field in kwargs:
                self.inputs[i] = float(kwargs[field])

    def __getattr__(self, k):
        if len(k) == 1 and ord('a') <= ord(k) and ord(k) <= ord('l'):
            return self.inputs[ord(k) - ord('a')]
        else:
            super(Calc, self).__getattr__(k)

    def __setattr__(self, k, v):
        if len(k) == 1 and ord('a') <= ord(k) and ord(k) <= ord('l'):
            self.inputs[ord(k) - ord('a')] = v
        else:
            super(Calc, self).__setattr__(k, v)

    def process_impl(self):
        super(Calc, self).process_impl()

        dct = {}
        for i in range(12):
            if self.in_links[i] is not None:
                self.inputs[i] = self.in_links[i].get()

            key = chr(ord('A') + i)
            dct[key] = self.inputs[i]

        self.result = eval(self.formula, dct, {})

class CalcOut(Calc):
    def __init__(self, **kwargs):
        super(CalcOut, self).__init__(**kwargs)
        self.out_formula = kwargs.get('ocal')
        self.out_link = make_link(kwargs.get('out'), self)

    def process_impl(self):
        super(CalcOut, self).process_impl()

        if self.out_formula is None:
            out_value = self.result
        else:
            dct = dict((chr(ord('A') + i), self.inputs[i]) for i in range(12))
            out_value = eval(self.out_formula, dct, {})

        if self.out_link is not None:
            self.out_link.set(out_value)

if __name__ == '__main__':
    import sys
    db = Database()
    ctx = {
            'db': db,
            'Calc': Calc,
            'CalcOut': CalcOut,
            }
    exec(sys.stdin.read(), ctx, {})

    print('initial:\t%r' % (list((k, v.result) for k,v in sorted(db.db.items())),))

    for i in range(len(sys.argv) - 1):
        arg = sys.argv[1 + i]

        k, _, v = arg.rpartition('=')
        name, dot, field = k.rpartition('.')
        if not dot:
            name = field.lower()
            field = 'result'
        setattr(db.get(name), field, float(v))
        print('(%d) %s:\t%r' % (i, arg,
            list((k, v.result) for k,v in sorted(db.db.items()))))

    print('final:\t%r' % (list((k, v.result) for k,v in sorted(db.db.items())),))
