# -*- generated by 1.1.0b13 -*-
import da
PatternExpr_260 = da.pat.TuplePattern([da.pat.ConstantPattern('ack')])
PatternExpr_265 = da.pat.FreePattern('s')
PatternExpr_310 = da.pat.TuplePattern([da.pat.ConstantPattern('push'), da.pat.FreePattern('secrets'), da.pat.FreePattern('predecessorsSecret'), da.pat.FreePattern('predecessor')])
PatternExpr_352 = da.pat.TuplePattern([da.pat.ConstantPattern('done')])
PatternExpr_357 = da.pat.SelfPattern()
PatternExpr_382 = da.pat.TuplePattern([da.pat.ConstantPattern('done')])
PatternExpr_387 = da.pat.BoundPattern('_BoundPattern389_')
PatternExpr_360 = da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.FreePattern(None), da.pat.SelfPattern()]), da.pat.TuplePattern([da.pat.ConstantPattern('done')])])
PatternExpr_390 = da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.TuplePattern([da.pat.FreePattern(None), da.pat.FreePattern(None), da.pat.BoundPattern('_BoundPattern396_')]), da.pat.TuplePattern([da.pat.ConstantPattern('done')])])
_config_object = {}
import sys
import time
'\nclass for Ring protocol 3, where:\nAgent i calls his successor, agent i âŠ• 1, if i is not familiar with all the secrets or i does not\nknow that his successor is familiar with the secret of his predecessor, agent iâŠ–1.\nThis protocol follows push mode of communication\n'

class DR3(da.DistProcess):

    def __init__(self, procimpl, forwarder, **props):
        super().__init__(procimpl, forwarder, **props)
        self._DR3ReceivedEvent_0 = []
        self._DR3ReceivedEvent_2 = []
        self._DR3ReceivedEvent_3 = []
        self._events.extend([da.pat.EventPattern(da.pat.ReceivedEvent, '_DR3ReceivedEvent_0', PatternExpr_260, sources=[PatternExpr_265], destinations=None, timestamps=None, record_history=True, handlers=[]), da.pat.EventPattern(da.pat.ReceivedEvent, '_DR3ReceivedEvent_1', PatternExpr_310, sources=None, destinations=None, timestamps=None, record_history=None, handlers=[self._DR3_handler_309]), da.pat.EventPattern(da.pat.ReceivedEvent, '_DR3ReceivedEvent_2', PatternExpr_352, sources=[PatternExpr_357], destinations=None, timestamps=None, record_history=True, handlers=[]), da.pat.EventPattern(da.pat.ReceivedEvent, '_DR3ReceivedEvent_3', PatternExpr_382, sources=[PatternExpr_387], destinations=None, timestamps=None, record_history=True, handlers=[])])

    def setup(self, successor, secret, t, n, mLoss, mDelay, **rest_418):
        super().setup(successor=successor, secret=secret, t=t, n=n, mLoss=mLoss, mDelay=mDelay, **rest_418)
        self._state.successor = successor
        self._state.secret = secret
        self._state.t = t
        self._state.n = n
        self._state.mLoss = mLoss
        self._state.mDelay = mDelay
        self._state.knownSecrets = set()
        self._state.knowsPredcessorsSecret = False
        self._state.predecessorSecret = list()
        self._state.knownSecrets.add(self._state.secret)
        self._state.count = 0

    def run(self):
        while (not PatternExpr_360.match_iter(self._DR3ReceivedEvent_2, SELF_ID=self._id)):
            self.gossip()
        self.send(('done',), to=self.parent())
        super()._label('_st_label_379', block=False)
        _st_label_379 = 0
        while (_st_label_379 == 0):
            _st_label_379 += 1
            if PatternExpr_390.match_iter(self._DR3ReceivedEvent_3, _BoundPattern396_=self.parent(), SELF_ID=self._id):
                _st_label_379 += 1
            else:
                super()._label('_st_label_379', block=True)
                _st_label_379 -= 1
        'Correctness Test: \n\t\tIf the number of known/learned secrets are equal to the total number of agents in the network,\n\t\tthen an agent is an expert and the protocol is correct\n\t\t'
        if (self._state.n == len(self._state.knownSecrets)):
            print('<DR3>Testing correctness; Number of secrets learnt equals Number of different processes, Result :Verified', flush=True)
        else:
            print('<DR3>Failed in correctness testing', flush=True)

    def gossip(self):
        ' \n\t\tCore function of the protocol, contains the protocol specific logic.\n\t\tAgent i calls his successor, agent i âŠ• 1, if i is not familiar with all the secrets or i does not\n\t\tknow that his successor is familiar with the secret of his predecessor, agent iâŠ–1.\n\t\tThis protocol follows push mode of communication\n\t\t'
        super()._label('yeild', block=False)
        " Agent checks that if he is not familiar with all the secrets\n\t\tor his successor doesnot know his predecessor's secret then the agent\n\t\tpushes its own secret to his successor "
        if ((not self._state.knowsPredcessorsSecret) or (not (len(self._state.knownSecrets) == self._state.n))):
            pushedSecrets = set(self._state.knownSecrets)
            print('{} sending secrets to {}'.format(self._id, self._state.successor), flush=True)
            self.send(('push', pushedSecrets, self._state.secret, self._id), to=self._state.successor)
            self._state.count = (self._state.count + 1)
            super()._label('_st_label_255', block=False)
            _st_label_255 = 0
            while (_st_label_255 == 0):
                _st_label_255 += 1
                if (len({s for (_, (_, _, s), (_ConstantPattern276_,)) in self._DR3ReceivedEvent_0 if (_ConstantPattern276_ == 'ack')}) == self._state.count):
                    pass
                    _st_label_255 += 1
                elif self._timer_expired:
                    print('timeout', flush=True)
                    _st_label_255 += 1
                else:
                    super()._label('_st_label_255', block=True, timeout=self._state.t)
                    _st_label_255 -= 1
            self._timer_start()
            if (self._state.predecessorSecret and (self._state.predecessorSecret[0] in pushedSecrets)):
                self._state.knowsPredcessorsSecret = True
        else:
            self.send(('done',), to=self._id)

    def _DR3_handler_309(self, secrets, predecessorsSecret, predecessor):
        print('{} receiving secrets from {}'.format(self._id, predecessor), flush=True)
        self.send(('ack',), to=predecessor)
        self._state.predecessorSecret.append(predecessorsSecret)
        self._state.knownSecrets = self._state.knownSecrets.union(secrets)
    _DR3_handler_309._labels = None
    _DR3_handler_309._notlabels = None
