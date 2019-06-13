from __future__ import division
from math import factorial, ceil
from itertools import product, combinations
import pylgl
#from IPython import embed
n = 3
m = 4
k = 3

litcount = 0
lit2int = {}
int2lit = {}

def allVoters():
    return range(n)

def allAlternatives():
    return range(m)

def allBallots():
    r = product(*([[0,1]]*m))
    return [x for x in r if x not in [tuple([0]*m), tuple([1]*m)]]

def allProfiles():
    return product(*([list(allBallots())]*n))

def allCommittees():
    return combinations(allAlternatives(), k)

def addApproval(voter, profile, candidates):
    profile = list(profile)
    new_profile = []
    current_voter = 0
    for ballot in profile:
        if current_voter != voter:
            new_profile.append(ballot)
        else:
            new_ballot = []
            for i in range(m):
                if i in candidates:
                    new_ballot.append(1)
                else:
                    new_ballot.append(ballot[i])
            new_profile.append(tuple(new_ballot))
        current_voter += 1
    return tuple(new_profile)

def singletonBallot(a):
    ballot = [0]*m
    ballot[a] = 1
    return tuple(ballot)

def approves(voter, alternative, profile):
    return profile[voter][alternative]

def ivariants(voter, profile):
    result = []
    for p in allProfiles():
        ivar = True
        for v in allVoters():
            if v==voter:
                continue
            if p[v] != profile[v]:
                ivar=False
                break
        if ivar:
            result.append(p)
    return result

def approvalCount(voter, profile, committee):
    return sum([profile[voter][x] for x in committee])

def isSubsetOf(ballot1, ballot2, strict=True):
    for b1,b2 in zip(ballot1, ballot2):
        if b1 and not b2:
            return False
        if b2 and not b1:
            strict = False
    
    if strict:
        return False
    else:
        return True

def intersection(committee, ballot):
    result = list(ballot)
    for i in allAlternatives():
        if not i in committee:
            result[i] = 0
    return tuple(result)

def strictlyBetter(voter, committee1, committee2, profile):
    """
    Returns True if committee 2 is strictly better than committee 1, for a
    certain voter according to a certain (truthful for i) ballotprofile
    """
    return isSubsetOf(intersection(committee1, profile[voter]), intersection(committee2, profile[voter]))

def toBinaryTuple(subset):
    result = []
    for i in range(m):
        if i in subset:
            result.append(1)
        else:
            result.append(0)
    return tuple(result)

def toSubset(binaryTuple):
    subset = []
    for i in range(m):
        if binaryTuple[i]:
            subset.append(i)
    return tuple(subset)


def subsetOf(superset, subset):
    for i in range(m):
        if superset[i] == 0 and subset[i] == 1:
            return False
    return True

def isPartylistProfile(profile):
    """
    A profile is a party-list profile iff, after removing duplicate ballots,
    there is no more overlap in the ballots
    """

    unique_ballots = set(profile)
    for e in zip(*unique_ballots):
        if sum(e)>1:
            return False
    return True


def posLiteral(committee, profile):
    global litcount, lit2int, int2lit

    if (committee, profile) in lit2int:
        return lit2int[(committee, profile)]
    else:
        litcount+=1
        lit2int[(committee, profile)] = litcount
        int2lit[litcount] = (committee, profile)
        return litcount

def negLiteral(committee, profile):
    return -posLiteral(committee, profile)


def cnfSSMWOPI():
    # Existence condition
    cnf = []
    for p in allProfiles():
        for G in allBallots():
            if sum(G) < k:
                for i in allVoters():
                    if intersection(toSubset(p[i]), G) == tuple([0]*m):
                        for W in allBallots():
                            if subsetOf(G, W):
                                clause = [negLiteral(toSubset(W), p)]
                                for Wprime in allBallots():
                                    if subsetOf(G, Wprime):
                                        clause.append(posLiteral(toSubset(Wprime), addApproval(i, p, toSubset(G))))
                                cnf.append(clause)


    # Universal condition
    for p in allProfiles():
        for G in allBallots():
            if sum(G) < k:
                for i in allVoters():
                    if intersection(toSubset(p[i]), G) == tuple([0]*m):
                        for Wprime in allBallots():
                            if not subsetOf(G, Wprime):
                                clause = [negLiteral(toSubset(Wprime), addApproval(i, p, toSubset(G)))]
                                for W in allBallots():
                                    if not subsetOf(G, Wprime):
                                        clause.append(posLiteral(toSubset(W), p))
                                cnf.append(clause)
    return cnf


def cnfStrategyproofness():
    """
    This axiom currently works according to "Strategyproofness" in D. Peters' 
    paper, and therefore (might) assume resoluteness
    """
    cnf = []
    for i in allVoters():
        for p1 in allProfiles():
            for p2 in ivariants(i, p1):
                if isSubsetOf(p2[i], p1[i]):
                    for c1 in allCommittees():
                        for c2 in allCommittees():
                            if strictlyBetter(i, c1, c2, p1):
                                cnf.append([negLiteral(c1, p1), negLiteral(c2, p2)])
    return cnf

def cnfProportionality():
    """
    Corresponds to Peters' weakest proportionality axiom, which he calls 
    "proportionality", assumes resoluteness
    """
    cnf = []
    for p in allProfiles():
        if isPartylistProfile(p):
            for a in allAlternatives():
                if p.count(singletonBallot(a)) >= ceil(n/k):
                    clause = []
                    for c in allCommittees():
                        if a in c:
                            clause.append(posLiteral(c, p))
                    cnf.append(clause)
    return cnf

def cnfProportionality2():
    """
    Corresponds to Peters' weakest proportionality axiom, which he calls 
    "proportionality"
    """
    cnf = []
    for p in allProfiles():
        if isPartylistProfile(p):
            for a in allAlternatives():
                if p.count(singletonBallot(a)) >= ceil(n/k):
                    for c in allCommittees():
                        if a not in c:
                            cnf.append([negLiteral(c, p)])
    return cnf

def cnfAtLeastOne():
    cnf = []
    for r in allProfiles():
        clause = []
        for c in allCommittees():
            clause.append(posLiteral(c, r))
        cnf.append(clause)
    return cnf

def cnfResolute():
    cnf = []
    for r in allProfiles():
        for c1,c2 in combinations(allCommittees(), 2):
            cnf.append([negLiteral(c1, r), negLiteral(c2, r)])
    return cnf

if __name__ == '__main__':
    #embed()
    cnf = []
    cnf += cnfAtLeastOne()
    #cnf += cnfResolute()
    #cnf += cnfStrategyproofness()
    cnf += cnfProportionality2()
    cnf += cnfSSMWOPI()
    ans = pylgl.solve(cnf)
    a = sorted([x for x in ans if x>0])
    for i in a:
        l = int2lit[i]
        #if l[0] != (0,1,2):
        print(l)
