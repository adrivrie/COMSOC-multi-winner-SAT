from __future__ import division
from math import factorial, ceil
from itertools import product, combinations, permutations
import pylgl
from sys import stderr
from tqdm import tqdm
from IPython import embed
import os
import pickle
import inspect

def cache(cachefile):
    """
    A function that creates a decorator which will use "cachefile" for caching the results of the decorated function "fn".
    """
    def decorator(fn):  # define a decorator for a function "fn"
        def wrapped(*args, **kwargs):   # define a wrapper that will finally call "fn" with all arguments            
            # if cache exists -> load it and return its content
            # except if contents of function have changed
            if os.path.exists(cachefile):
                with open(cachefile, 'rb') as cachehandle:
                    contents = pickle.load(cachehandle)
                    if contents[1] == inspect.getsource(fn):
                        return contents[0]

            # execute the function with all arguments passed
            res = fn(*args, **kwargs)

            # write to cache file
            with open(cachefile, 'wb') as cachehandle:
                print("saving result to cache '%s'" % cachefile)
                pickle.dump((res, inspect.getsource(fn)), cachehandle)

            return res

        return wrapped

    return decorator


n=3
m=4
k0 = m-1
k1 = m

# this has to remain this way, lots of dependency on this, change k0 and k1
ks = range(k0, k1)

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

def permuteBallot(ballot, perm):
    permBallot = []
    for alt in allAlternatives():
        permBallot.append(ballot[perm[alt]])
    return tuple(permBallot)

def candidatePerms(profile, committee):
    perms = permutations(allAlternatives())
    permProfiles = []
    for perm in perms:
        permProfile = []
        for ballot in profile:
            permBallot = permuteBallot(ballot, perm)
            permProfile.append(permBallot)

        permCommittee = permuteBallot(committee, perm)
        permProfiles.append((tuple(permProfile), permCommittee))

    return permProfiles


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

def sortedProfile(profile):
    profile = list(profile)
    sortedProfile = sorted(profile)
    return tuple(sortedProfile)

def cnfNeutrality():
    cnf = []

    permDict = {}
    for p in allProfiles():
        for c in allCommittees():
            if p in permDict:
                continue
            for perm in candidatePerms(p, c):
                permDict[perm] = (p, c)

    for p in allProfiles():
        for c in allCommittees():
            permP = permDict[(p, c)][0]
            permC = permDict[(p, c)][1]

            cnf.append([negLiteral(c, p), posLiteral(permC, permP)])
            cnf.append([posLiteral(c, p), negLiteral(permC, permP)])

    return cnf

def cnfAnonymity():
    cnf = []
    for p in allProfiles():
        for c in allCommittees():
            sp = sortedProfile(p)
            cnf.append([negLiteral(c, p), posLiteral(c, sp)])
            cnf.append([posLiteral(c, p), negLiteral(c, sp)])
    return cnf

@cache("cnf_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
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

@cache("cnf_optim_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
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

@cache("cnf_pess_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
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

@cache("cnf_proportionality_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
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

def strictlyDominates(profile, committee1, committee2):
    strict = False
    for ballot in profile:
        card1 = cardinalityOfOverlap(ballot, committee1)
        card2 = cardinalityOfOverlap(ballot, committee2)
        if card1 < card2:
            return False
        elif card1 > card2:
            strict = True
    return strict


def cnfParetoEfficiency():
    cnf=[]
    for profile in tqdm(list(allProfiles())):
        for k in ks:
            for committee1 in allCommitteesOfSize(k):
                for committee2 in allCommitteesOfSize(k):
                    if strictlyDominates(profile, committee1, committee2):
                        cnf.append([negLiteral(committee2, profile)])
    return cnf


def cnfCommitteeMonotonicity():
    cnf  = []

    for profile in tqdm(list(allProfiles())):    
        
        # from k to k+1
        for k in ks[:-1]:
            for c1 in allCommitteesOfSize(k):
                clause = [negLiteral(c1, profile)]
                for c2 in allCommitteesOfSize(k+1):
                    if isSubsetOf(c1, c2):
                        clause.append(posLiteral(c2, profile))
                cnf.append(clause)

        # from k+1 to k
        for k in ks[1:]:
            for c1 in allCommitteesOfSize(k):
                clause = [negLiteral(c1, profile)]
                for c2 in allCommitteesOfSize(k-1):
                    if isSubsetOf(c2, c1):
                        clause.append(posLiteral(c2, profile))
                cnf.append(clause)
    return cnf

def votesForCommittee(profile, committee):
    c=0
    for ballot in profile:
        c+= cardinalityOfOverlap(ballot, committee)
    return c

def cnfTiebreakInFavorOfMoreVotes():
    cnf = []
    for profile in tqdm(list(allProfiles())):
        for k in ks:
            for committee1 in allCommitteesOfSize(k):
                for committee2 in allCommitteesOfSize(k):
                    if votesForCommittee(profile, committee1) != votesForCommittee(profile, committee2):
                        cnf.append([negLiteral(committee1, profile), negLiteral(committee2, profile)])
    return cnf


# leave this for reasons
cnfAtLeastOne()


if __name__ == '__main__':
    cnf = []
    print("cnfAtLeastOne:", file=stderr)
    cnf += cnfAtLeastOne()
    #print("cnfResolute:", file=stderr)
    #cnf += cnfResolute()
    #print("cnfStrategyproofness:", file=stderr)
    #cnf += cnfStrategyproofness()
    print("cnfAnonymity", file=stderr)
    cnf += cnfAnonymity()
    print("cnfNeutrality", file=stderr)
    cnf += cnfNeutrality()
    #print('cnfProportionality:', file=stderr)
    #cnf += cnfProportionality()
    #print("cnfPAV")
    #cnf += cnfPAV()
    #print("cnfJustifiedRepresentation", file=stderr)
    #cnf += cnfJustifiedRepresentation()
    print("cnfExtendedJustifiedRepresentation", file=stderr)
    cnf += cnfExtendedJustifiedRepresentation()
    print("cnfPessimisticCardinalityStrategyproofness", file=stderr)
    cnf += cnfPessimisticCardinalityStrategyproofness()
    print('cnfOptimisticCardinalityStrategyproofness', file=stderr)
    cnf += cnfOptimisticCardinalityStrategyproofness()
    #print("cnfCommitteeMonotonicity:", file=stderr)
    #cnf += cnfCommitteeMonotonicity()
    print("cnfParetoEfficiency", file=stderr)
    cnf += cnfParetoEfficiency()
    #print("cnfTiebreakInFavorOfMoreVotes")
    #cnf += cnfTiebreakInFavorOfMoreVotes()

    # Change if you want to get the clauses in file format
    if False:
        print("p cnf {0} {1}".format(litcount, len(cnf)))
    
        for clause in cnf:
            clause = [str(c) for c in clause]
            print(' '.join(clause) + ' 0')

    
    else:
    
        print("Solving...", file=stderr)


        counter = 0
        
        sol_list = []

        for sol in pylgl.itersolve(cnf):
            if(counter % 100 == 0):
                print(counter)
            a = sorted([int2lit[x] for x in sol if x > 0])
            sol_list.append(a)
            counter += 1
        print(counter)


        with open("rule-dump.pkl", 'wb') as h:
            pickle.dump(sol_list, h)

        #embed()

        """ans = pylgl.solve(cnf)
        a = sorted([x for x in ans if x>0])
        for i in a:
            l = int2lit[i]
            #if l[0] != (0,1,2):
            print("{} elects: {}".format(l[1], l[0]))"""





