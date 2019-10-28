from __future__ import division
from math import factorial, ceil
from fractions import Fraction
from itertools import product, combinations, permutations, chain
from sys import stderr
from copy import deepcopy

#PARAMS
n=4
m=4

# this sets the starting and end value, for if you want more than 1 value of k. m-1 and m give only k=m-1
k0 = m-1
k1 = m

# this has to remain this way, lots of dependency on this, change k0 and k1
ks = range(k0, k1)

# necessary for converting python objects to ints (which pylgl wants)
# also for transofmring back


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
    for c in combinations(range(m), k):
        com = [0]*m
        for i in c:
            com[i] = 1
        yield tuple(com)

def allWinningSets():
    s = list(allCommittees())
    # from itertools recipe for powerset
    for W in chain.from_iterable(combinations(s, r) for r in range(len(s)+1)):
        #only non-empty winning sets are allowed
        if W:
            yield W

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
    ivar = list(profile)
    for ballot in allBallots():
        result = deepcopy(ivar)
        result[voter] = ballot
        yield tuple(result)


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

    return intersection(successes1, successes2) == successes1 and successes2 != successes1


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

def sortedProfile(profile):
    """
    Returns a sorted version of the profile, not in-place, and still tuple
    """
    profile = list(profile)
    sortedProfile = sorted(profile)
    return tuple(sortedProfile)

def cardinalityOfOverlap(ballot, committee):
    """
    Gives the amount of approved candidates in committee according to ballot
    """
    c=0
    for candidate, vote in zip(committee, ballot):
        c += (candidate and vote) 
    return c

def strictlySupersetDominates(profile, committee1, committee2):
    """
    Returns true if committee1 strictly dominates committee2 in the sense
    of weak Pareto
    """
    strict = False
    for voter, ballot in enumerate(profile):
        int1 = intersection(ballot, committee1)
        int2 = intersection(ballot, committee2)
        for i1, i2 in zip(int1, int2):
            if i2 > i1:
                return False
            if i1 > i2:
                strict = True
    return strict

def satisfiesJR(committee, profile, debug=False):
    """
    Return true if the committee, given the profile, satisfies JR
    """
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

def satisfiesEJR(committee, profile):
    """
    Returns true if committee satisfies Extended Justified Representation
    for profile

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

def strictlyDominates(profile, committee1, committee2):
    """
    Checks if every voter has at least as many of their candidates
    in committee1 as in committee2, and at least one has strictly
    more
    """
    strict = False
    for ballot in profile:
        card1 = cardinalityOfOverlap(ballot, committee1)
        card2 = cardinalityOfOverlap(ballot, committee2)
        if card1 < card2:
            return False
        elif card1 > card2:
            strict = True
    return strict

def votesForCommittee(profile, committee):
    """
    Gives AV score for the committee
    """
    c=0
    for ballot in profile:
        c+= cardinalityOfOverlap(ballot, committee)
    return c

def meanCardinality(winning_set, ballot):
    result = Fraction(0)
    for committee in winning_set:
        result += cardinalityOfOverlap(ballot, committee)
    return result / len(winning_set)
