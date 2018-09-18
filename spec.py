import sys
config(channel= 'fifo', clock= 'Lamport')

class P(process):
    def setup(s:set, nrequests:int): pass  # s is set of all other processes

    def mutex(task):
        -- request
        c = logical_clock()
        send(('request', c, self), to= s)
        await(each(received(('request', c2, p)),
                   has= received(('release', c2, p)) or (c, self) < (c2, p))
              and each(p in s, has= received(('ack', c, p))))
        -- critical_section
        task()
        -- release
        send(('release', c, self), to= s)

    def receive(msg= ('request', c, p)):
        send(('ack', c, self), to= p)

    def run():
        def task():
            output('in cs')
            output('releasing cs')
        for i in range(nrequests):
            mutex(task)

        send(('done', self), to= s)
        await(each(p in s, has= received(('done', p))))
        output('terminating')

def main():
    nprocs = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    nrequests = int(sys.argv[2]) if len(sys.argv) > 2 else 1

    ps = new(P, num= nprocs)
    for p in ps: setup(p, (ps-{p}, nrequests))
    start(ps)
