# -*- generated by 1.1.0b13 -*-
import da
PatternExpr_275 = da.pat.TuplePattern([da.pat.ConstantPattern('push'), da.pat.FreePattern(None), da.pat.FreePattern('ele')])
PatternExpr_282 = da.pat.FreePattern('ele')
PatternExpr_313 = da.pat.TuplePattern([da.pat.ConstantPattern('push'), da.pat.FreePattern('secret_entries'), da.pat.FreePattern('p')])
PatternExpr_353 = da.pat.TuplePattern([da.pat.ConstantPattern('pull'), da.pat.FreePattern('p')])
PatternExpr_392 = da.pat.TuplePattern([da.pat.ConstantPattern('done')])
PatternExpr_397 = da.pat.BoundPattern('_BoundPattern399_')
PatternExpr_400 = da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.FreePattern(None), da.pat.BoundPattern('_BoundPattern406_')]), da.pat.TuplePattern([da.pat.ConstantPattern('done')])])
_config_object = {}
import sys
import glob
import os
import time
from random import randint
'\nclass for Learn New Secret, where:\nAgent i calls agent j if i is not familiar with jâ€™s secret\nThis protocol follows pull mode of communication\n'

class LNS(da.DistProcess):

    def __init__(self, procimpl, forwarder, **props):
        super().__init__(procimpl, forwarder, **props)
        self._LNSReceivedEvent_0 = []
        self._LNSReceivedEvent_3 = []
        self._events.extend([da.pat.EventPattern(da.pat.ReceivedEvent, '_LNSReceivedEvent_0', PatternExpr_275, sources=[PatternExpr_282], destinations=None, timestamps=None, record_history=True, handlers=[]), da.pat.EventPattern(da.pat.ReceivedEvent, '_LNSReceivedEvent_1', PatternExpr_313, sources=None, destinations=None, timestamps=None, record_history=None, handlers=[self._LNS_handler_312]), da.pat.EventPattern(da.pat.ReceivedEvent, '_LNSReceivedEvent_2', PatternExpr_353, sources=None, destinations=None, timestamps=None, record_history=None, handlers=[self._LNS_handler_352]), da.pat.EventPattern(da.pat.ReceivedEvent, '_LNSReceivedEvent_3', PatternExpr_392, sources=[PatternExpr_397], destinations=None, timestamps=None, record_history=True, handlers=[])])

    def setup(self, s, secret, tout, n, mlossrate, msg_delay, **rest_431):
        super().setup(s=s, secret=secret, tout=tout, n=n, mlossrate=mlossrate, msg_delay=msg_delay, **rest_431)
        self._state.s = s
        self._state.secret = secret
        self._state.tout = tout
        self._state.n = n
        self._state.mlossrate = mlossrate
        self._state.msg_delay = msg_delay
        self._state.entries = {}
        for ele in self._state.s:
            self._state.entries[ele] = 0
        self._state.entries[self._id] = 1
        self._state.exitCondition = False

    def run(self):
        self.gossip()
        self.send(('done', self._id), to=self.parent())
        super()._label('_st_label_389', block=False)
        _st_label_389 = 0
        while (_st_label_389 == 0):
            _st_label_389 += 1
            if PatternExpr_400.match_iter(self._LNSReceivedEvent_3, _BoundPattern406_=self.parent(), SELF_ID=self._id):
                _st_label_389 += 1
            else:
                super()._label('_st_label_389', block=True)
                _st_label_389 -= 1
        'Correctness Test: \n\t\tIf the number of known/learned secrets are equal to the total number of agents in the network,\n\t\tthen an agent is an expert and the protocol is correct\n\t\t'
        if (sum(self._state.entries.values()) == len(self._state.entries)):
            print('<LNS>Testing correctness; Number of secrets learnt equals Number of different processes, Result :Verified', flush=True)
        else:
            print('<LNS>Failed in correctness testing', flush=True)

    def gossip(self):
        '\n\t\tCore function of the protocol Learn New Secret, contains the protocol specific logic.\n\t\tAgent i calls agent j if i is not familiar with jâ€™s secret\n\t\tThis protocol follows pull mode of communication\n\t\t'
        count = 1
        'Keep gossiping until the agent knows/learned all other secrets'
        while 1:
            self._state.exitCondition = True
            for ele in self._state.entries:
                if (self._state.entries[ele] == 0):
                    self._state.exitCondition = False
                    print('{} sending pull request to {}'.format(self._id, ele), flush=True)
                    self.send(('pull', self._id), to=ele)
                    super()._label('_st_label_270', block=False)
                    _st_label_270 = 0
                    while (_st_label_270 == 0):
                        _st_label_270 += 1
                        if (len({ele for (_, (_, _, ele), (_ConstantPattern292_, _, _FreePattern295_)) in self._LNSReceivedEvent_0 if (_ConstantPattern292_ == 'push') if (_FreePattern295_ == ele)}) == count):
                            count += 1
                            _st_label_270 += 1
                        elif self._timer_expired:
                            pass
                            _st_label_270 += 1
                        else:
                            super()._label('_st_label_270', block=True, timeout=self._state.tout)
                            _st_label_270 -= 1
                    else:
                        if (_st_label_270 != 2):
                            continue
                    self._timer_start()
                    if (_st_label_270 != 2):
                        break
            if self._state.exitCondition:
                break

    def _LNS_handler_312(self, secret_entries, p):
        print('{} receiving secret entries from {}, begins upating its entires'.format(self._id, p), flush=True)
        for ele2 in secret_entries:
            if (secret_entries[ele2] == 1):
                self._state.entries[ele2] = 1
    _LNS_handler_312._labels = None
    _LNS_handler_312._notlabels = None

    def _LNS_handler_352(self, p):
        print('{} sending request secret to {}'.format(self._id, p), flush=True)
        self.send(('push', self._state.entries, self._id), to=p)
    _LNS_handler_352._labels = None
    _LNS_handler_352._notlabels = None