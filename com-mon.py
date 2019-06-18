from __future__ import division
from math import factorial, ceil
from itertools import product, combinations
import pylgl
from tqdm import tqdm
from IPython import embed
n=3
m=4
ks = range(1, m)

litcount = 0
lit2int = {}
int2lit = {}

def allVoters():
    return range(n)

def allAlternatives():
    return range(m)

def allBallots():
    r = product(*([[0,1]]*m))
    return r

def allProfiles():
    return product(*([list(allBallots())]*n))

def allCommittees():
    for b in allBallots():
        if sum(b) in ks:
            yield b

def allCommitteesOfSize(k):
    for b in allBallots():
        if sum(b) == k:
            yield b

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
    c=0
    for vote,com in zip(profile[voter], committee):
        if vote and com:
            c+=1
    return c

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
    result = []

    for c,v in zip(committee, ballot):
        if c and v:
            result.append(1)
        else:
            result.append(0)
    return tuple(result)

def strictlyBetter(voter, committee1, committee2, profile):
    """
    Returns True if committee 2 is strictly better than committee 1, for a
    certain voter according to a certain (truthful for i) ballotprofile
    """
    successes1 = intersection(committee1, profile[voter])
    successes2 = intersection(committee2, profile[voter])

    return intersection(successes1, successes2) == successes2 and successes2 != successes1


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

def PAVscore(profile, committee):
    """
    For very, very large k (>300) this function does not work well enough
    because of floating point errors
    """
    score = 0
    for voter in profile:
        approvecount = 0
        for elected,vote in zip(committee, voter):
            if vote and elected:
                approvecount+=1
        for i in range(approvecount):
            score+=(1/(i+1))
    return score

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

def cnfPAV():
    """
    Calculates the PAV score, and returns a negative literal for those
    committees that do not maximize it.

    Not as fast as it can be, but clear and not a bottleneck.
    """


    cnf  = []
    for p in tqdm(list(allProfiles())):
        for k in ks:
            comscore = []
            # get all scores
            for c in allCommitteesOfSize(k):
                score = PAVscore(p,c)
                comscore.append((c, score))
            # calculate the maximum score
            maxscore = 0
            for c,s in comscore:
                maxscore = max(maxscore, s)
            # add all suboptimal committees as neglits
            for c,s in comscore:
                if s + 1e-5 < maxscore:
                    cnf.append([negLiteral(c,p)])
    return cnf

def cnfStrategyproofness():
    """
    This axiom currently works according to "Strategyproofness" in D. Peters' 
    paper, and therefore (might) assume resoluteness
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():

            for p2 in ivariants(i, p1):
                if isSubsetOf(p2[i], p1[i]):
                    for c1 in allCommittees():
                        k = sum(c1)
                        for c2 in allCommitteesOfSize(k):
                            if strictlyBetter(i, c1, c2, p1):
                                cnf.append([negLiteral(c1, p1), negLiteral(c2, p2)])
    return cnf

def cardinalityOfOverlap(ballot, committee):
    c=0
    for candidate, vote in zip(committee, ballot):
        c += (candidate and vote) 
    return c

def cnfOptimisticCardinalityStrategyproofness():
    cnf  = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for c2 in allCommittees():
                    k = sum(c2)
                    clause = [negLiteral(c2, p2)]
                    card = cardinalityOfOverlap(p1[i], c2)
                    for c1 in allCommitteesOfSize(k):
                        if cardinalityOfOverlap(p1[i], c1) >= card:
                            clause.append(posLiteral(c1, p1))
                    cnf.append(clause)
    return cnf

def cnfPessimisticCardinalityStrategyproofness():
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for c1 in allCommittees():
                    k = sum(c1)
                    clause = [negLiteral(c1, p1)]
                    card = cardinalityOfOverlap(p1[i], c1)
                    for c2 in allCommitteesOfSize(k):
                        if cardinalityOfOverlap(p2[i],c2) <= card:
                            clause.append(posLiteral(c2, p2))
    return cnf

def cnfProportionality():
    """
    Corresponds to Peters' weakest proportionality axiom, which he calls 
    "proportionality"

    In the irresolute case, states that all winners should satisfy
    proportionality
    """
    cnf = []
    for p in tqdm(list(allProfiles())):
        if isPartylistProfile(p):
            for a in allAlternatives():
                for k in ks:
                    if p.count(singletonBallot(a)) >= n/k-1e-5:
                        for c in allCommitteesOfSize(k):
                            if not c[a]:
                                cnf.append([negLiteral(c, p)])
    return cnf

def satisfiesJR(committee, profile, debug=False):
    k = sum(committee)
    threshold = n/k - 1e-5
    uncovered_ballots = []
    for ballot in profile:
        for vote, elected in zip(ballot, committee):
            if vote and elected:
                break
        else:
            uncovered_ballots.append(ballot)
    votespercandidate = [0]*m
    for ballot in uncovered_ballots:
        for candidate, vote in enumerate(ballot):
            votespercandidate[candidate]+=vote
    
    if max(votespercandidate) >= threshold:
        return False 
    else:
        return True

def cnfJustifiedRepresentation():
    """
    In irresolute case: all winners must satisfy
    """
    cnf = []
    for p in tqdm(list(allProfiles())):
        for c in allCommittees():
            if not satisfiesJR(c, p):
                cnf.append([negLiteral(c,p)])
    return cnf

# Note: assumes that both committee and profile are binary vectors
def satisfiesEJR(committee, profile):
    """
    This is coNP-complete
    """
    k = sum(committee)
    
    # calculate for each voter how many representatives he has in committee
    voterRepr = []
    for ballot in profile:
        representatives = 0
        for c,b in zip(committee, ballot):
            if c and b:
                representatives += 1
        voterRepr.append(representatives)

    for l in range(1, k+1):
        # calculate all voters with < l representatives
        underRepres = []
        for voter, repres in enumerate(voterRepr):
            if repres < l:
                underRepres.append(voter)

        minSize = ceil(l * (n/k) - 1e-5)

        # find all subsets of size l * (n/k)
        for comb in combinations(underRepres, minSize):
            
            # count how many alternatives they all agree on
            approveCount = 0
            for i in range(m):
                allApprove = True
                for voter in comb:
                    if profile[voter][i] != 1:
                        allApprove = False
                if allApprove:
                    approveCount += 1

            # this should not be >= l if it satisfies EJR
            if approveCount >= l:
                return False

    return True

def cnfExtendedJustifiedRepresentation():
    """
    In irresolute case: all winners must satisfy
    """
    cnf = []
    for p in tqdm(list(allProfiles())):
        for c in allCommittees():
            if not satisfiesEJR(c, p):
                cnf.append([negLiteral(c,p)])
    return cnf


def cnfAtLeastOne():
    cnf = []
    for r in tqdm(list(allProfiles())):
        for k in ks:
            clause = []
            for c in allCommitteesOfSize(k):
                clause.append(posLiteral(c, r))
            cnf.append(clause)
    return cnf

def cnfResolute():
    cnf = []
    for r in tqdm(list(allProfiles())):
        for k in ks:
            for c1,c2 in combinations(allCommitteesOfSize(k), 2):
                cnf.append([negLiteral(c1, r), negLiteral(c2, r)])
    return cnf



if __name__ == '__main__':
    cnf = []
    print("cnfAtLeastOne:")
    cnf += cnfAtLeastOne()
    print("cnfResolute:")
    cnf += cnfResolute()
    #print("cnfStrategyproofness:")
    #cnf += cnfStrategyproofness()
    #print('cnfProportionality:')
    #cnf += cnfProportionality()
    #cnf += cnfPAV()
    #print("cnfJustifiedRepresentation")
    #cnf += cnfJustifiedRepresentation()
    print("cnfExtendedJustifiedRepresentation")
    cnf += cnfExtendedJustifiedRepresentation()
    print("cnfPessimisticCardinalityStrategyproofness")
    cnf += cnfPessimisticCardinalityStrategyproofness()
    print('cnfOptimisticCardinalityStrategyproofness')
    cnf += cnfOptimisticCardinalityStrategyproofness()
    print("Solving...")
    ans = pylgl.solve(cnf)
    a = sorted([x for x in ans if x>0])
    for i in a:
        l = int2lit[i]
        #if l[0] != (0,1,2):
        print("{} elects: {}".format(l[1], l[0]))




