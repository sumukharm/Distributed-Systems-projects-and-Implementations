# -*- generated by 1.1.0b13 -*-
import da
PatternExpr_259 = da.pat.TuplePattern([da.pat.ConstantPattern('ack')])
PatternExpr_264 = da.pat.BoundPattern('_BoundPattern265_')
PatternExpr_311 = da.pat.TuplePattern([da.pat.ConstantPattern('push'), da.pat.FreePattern('secrets'), da.pat.FreePattern('predecessor')])
PatternExpr_346 = da.pat.TuplePattern([da.pat.ConstantPattern('done')])
PatternExpr_351 = da.pat.SelfPattern()
PatternExpr_371 = da.pat.TuplePattern([da.pat.ConstantPattern('done')])
PatternExpr_376 = da.pat.BoundPattern('_BoundPattern378_')
PatternExpr_354 = da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.FreePattern(None), da.pat.SelfPattern()]), da.pat.TuplePattern([da.pat.ConstantPattern('done')])])
PatternExpr_379 = da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.FreePattern(None), da.pat.BoundPattern('_BoundPattern385_')]), da.pat.TuplePattern([da.pat.ConstantPattern('done')])])
PatternExpr_266 = da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.FreePattern(None), da.pat.BoundPattern('_BoundPattern272_')]), da.pat.TuplePattern([da.pat.ConstantPattern('ack')])])
_config_object = {}
import sys
import time
from random import randint
from statistics import stdev
'\nclass for Ring protocol 4, where:\nAgent i calls his successor, agent iâŠ•1, if i is familiar with some secret and he does not know\nwhether his successor is familiar with it\nThis protocol follows push mode of communication\n'

class DR4(da.DistProcess):

    def __init__(self, procimpl, forwarder, **props):
        super().__init__(procimpl, forwarder, **props)
        self._DR4ReceivedEvent_0 = []
        self._DR4ReceivedEvent_2 = []
        self._DR4ReceivedEvent_3 = []
        self._events.extend([da.pat.EventPattern(da.pat.ReceivedEvent, '_DR4ReceivedEvent_0', PatternExpr_259, sources=[PatternExpr_264], destinations=None, timestamps=None, record_history=True, handlers=[]), da.pat.EventPattern(da.pat.ReceivedEvent, '_DR4ReceivedEvent_1', PatternExpr_311, sources=None, destinations=None, timestamps=None, record_history=None, handlers=[self._DR4_handler_310]), da.pat.EventPattern(da.pat.ReceivedEvent, '_DR4ReceivedEvent_2', PatternExpr_346, sources=[PatternExpr_351], destinations=None, timestamps=None, record_history=True, handlers=[]), da.pat.EventPattern(da.pat.ReceivedEvent, '_DR4ReceivedEvent_3', PatternExpr_371, sources=[PatternExpr_376], destinations=None, timestamps=None, record_history=True, handlers=[])])

    def setup(self, successor, secret, t, n, mLoss, mDelay, **rest_407):
        super().setup(successor=successor, secret=secret, t=t, n=n, mLoss=mLoss, mDelay=mDelay, **rest_407)
        self._state.successor = successor
        self._state.secret = secret
        self._state.t = t
        self._state.n = n
        self._state.mLoss = mLoss
        self._state.mDelay = mDelay
        self._state.successorSecrets = set()
        self._state.knownSecrets = set()
        self._state.exitCondition = False
        self._state.knownSecrets.add(self._state.secret)

    def run(self):
        while (not PatternExpr_354.match_iter(self._DR4ReceivedEvent_2, SELF_ID=self._id)):
            self.gossip()
        super()._label('_st_label_368', block=False)
        _st_label_368 = 0
        while (_st_label_368 == 0):
            _st_label_368 += 1
            if PatternExpr_379.match_iter(self._DR4ReceivedEvent_3, _BoundPattern385_=self.parent(), SELF_ID=self._id):
                _st_label_368 += 1
            else:
                super()._label('_st_label_368', block=True)
                _st_label_368 -= 1
        'Correctness Test: \n\t\tIf the number of known/learned secrets are equal to the total number of agents in the network,\n\t\tthen an agent is an expert and the protocol is correct\n\t\t'
        if (self._state.n == len(self._state.knownSecrets)):
            print('<DR4>Testing correctness; Number of secrets learnt equals Number of different processes, Result :Verified', flush=True)
        else:
            print('<DR4>Failed in correctness testing', flush=True)

    def gossip(self):
        ' \n\t\tCore function of the protocol, contains the protocol specific logic.\n\t\tAgent i calls his successor, agent iâŠ•1, if i is familiar with some secret and he does not know\n\t\twhether his successor is familiar with it\n\t\tThis protocol follows push mode of communication\n\t\t'
        super()._label('yeild', block=False)
        self._state.exitCondition = True
        ' Similar to protocol 1, Agent checks that if there exists a secret which he knows\n\t\tbut his/her successor is not aware, then he calls his/her successor '
        for knownSecret in self._state.knownSecrets:
            if (not (knownSecret in self._state.successorSecrets)):
                self._state.exitCondition = False
                print('{} sending secrets to {}'.format(self._id, self._state.successor), flush=True)
                pushedSecrets = set(self._state.knownSecrets)
                self.send(('push', pushedSecrets, self._id), to=self._state.successor)
                super()._label('_st_label_256', block=False)
                _st_label_256 = 0
                while (_st_label_256 == 0):
                    _st_label_256 += 1
                    if PatternExpr_266.match_iter(self._DR4ReceivedEvent_0, _BoundPattern272_=self._state.successor, SELF_ID=self._id):
                        self._state.successorSecrets = self._state.successorSecrets.union(pushedSecrets)
                        _st_label_256 += 1
                    elif self._timer_expired:
                        print('timeout', flush=True)
                        _st_label_256 += 1
                    else:
                        super()._label('_st_label_256', block=True, timeout=self._state.t)
                        _st_label_256 -= 1
                else:
                    if (_st_label_256 != 2):
                        continue
                self._timer_start()
                if (_st_label_256 != 2):
                    break
        if (self._state.exitCondition and (len(self._state.knownSecrets) == self._state.n)):
            self.send(('done',), to=self._id)
            self.send(('done',), to=self.parent())

    def _DR4_handler_310(self, secrets, predecessor):
        print('{} receiving secrets from {}'.format(self._id, predecessor), flush=True)
        self.send(('ack',), to=predecessor)
        self._state.knownSecrets = self._state.knownSecrets.union(secrets)
    _DR4_handler_310._labels = None
    _DR4_handler_310._notlabels = None