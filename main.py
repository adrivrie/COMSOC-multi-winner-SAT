from __future__ import division, print_function
from math import factorial, ceil
from itertools import product, combinations, permutations, chain
import pylgl
from sys import stderr
from tqdm import tqdm
from copy import deepcopy
from caching import cache
from helperfunctions import *
from dimacser import dimacs

# necessary for converting python objects to ints (which pylgl wants)
# also for transforming back
litcount = 0
lit2int = {}
int2lit = {}

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

@cache("cnf_propvotingrule_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfProportionalityVotingRule():
    """
    Requires every proportional committee to win, and every 
    non-proportional committee to lose. Therefore completely
    specifies a voting rule
    """
    cnf = []
    for p in tqdm(list(allProfiles())):
        for k in ks:
            for c in allCommitteesOfSize(k):
                negged = False
                if isPartylistProfile(p):
                    for a in allAlternatives():
                        if p.count(singletonBallot(a)) >= n/k-1e-5:
                            if not c[a]:
                                cnf.append([negLiteral(c, p)])
                                negged=True
                if not negged:
                    cnf.append([posLiteral(c, p)])
    return cnf

def cnfNeutrality():
    """
    Enforces neutrality, that is, a permutation of alternatives in the
    profile should not give a different result, except for applying the same
    permutation to the committee
    """
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
    """
    Any permutation of the ballot should give the same committees
    """
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


@cache("cnf_mean_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfMeanCardinalityStrategyproofness():
    """
    No voter should be able to increase their expected number of approved
    candidates by submitting an untruthful ballot, assuming uniformly
    random tie-breaking.

    Implementation is very complex (computationally), but I doubt it can
    be better.
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for X in allWinningSets():
                    for Y in allWinningSets():
                        if meanCardinality(Y, p1[i]) > meanCardinality(X, p1[i]):
                            X_is_not_winning_set_for_p1 = [negLiteral(c, p1) if c in X else posLiteral(c, p1) for c in allCommittees()]
                            Y_is_not_winning_set_for_p2 = [negLiteral(c, p2) if c in Y else posLiteral(c, p2) for c in allCommittees()]
                            cnf.append(X_is_not_winning_set_for_p1 + Y_is_not_winning_set_for_p2)
    return cnf


@cache("cnf_kellyweak_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfKellyWeakCardinalityStrategyproofness():
    """
    Implementation is very complex (computationally), but I doubt it can
    be better.
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for X in allWinningSets():
                    for Y in allWinningSets():
                        if minCardinality(Y, p1[i]) >= maxCardinality(X, p1[i]) and maxCardinality(Y, p1[i]) > minCardinality(X, p1[i]):
                            X_is_not_winning_set_for_p1 = [negLiteral(c, p1) if c in X else posLiteral(c, p1) for c in allCommittees()]
                            Y_is_not_winning_set_for_p2 = [negLiteral(c, p2) if c in Y else posLiteral(c, p2) for c in allCommittees()]
                            cnf.append(X_is_not_winning_set_for_p1 + Y_is_not_winning_set_for_p2)
    return cnf


@cache("cnf_kellyweak2_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfKellyWeak2CardinalityStrategyproofness():
    """
    Implementation is very complex (computationally), but I doubt it can
    be better.
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for X in allWinningSets():
                    for Y in allWinningSets():
                        if minCardinality(Y, p1[i]) >= maxCardinality(X, p1[i]) and maxCardinality(Y, p1[i]) > maxCardinality(X, p1[i]):
                            X_is_not_winning_set_for_p1 = [negLiteral(c, p1) if c in X else posLiteral(c, p1) for c in allCommittees()]
                            Y_is_not_winning_set_for_p2 = [negLiteral(c, p2) if c in Y else posLiteral(c, p2) for c in allCommittees()]
                            cnf.append(X_is_not_winning_set_for_p1 + Y_is_not_winning_set_for_p2)
    return cnf

@cache("cnf_kelly_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfKellyCardinalityStrategyproofness():
    """
    Cardinality-strategyproofness for Kelly ranking of sets
    """
    cnf  = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for c2 in allCommittees():
                    k = sum(c2)
                    card = cardinalityOfOverlap(p1[i], c2)
                    for c1 in allCommitteesOfSize(k):
                        if cardinalityOfOverlap(p1[i], c1) < card:
                            clause = [negLiteral(c2, p2), negLiteral(c1, p1)]
                            cnf.append(clause)
    return cnf


@cache("cnf_kelly_superset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfKellySupersetStrategyproofness():
    """
    Superset-strategyproofness for Kelly ranking of sets
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                for c1 in allCommittees():
                    k = sum(c1)
                    for c2 in allCommitteesOfSize(k):
                        if strictlyBetter(i, c1, c2, p1):
                            clause = [negLiteral(c1, p1), negLiteral(c2, p2)]
                            cnf.append(clause)
    return cnf

@cache("cnf_fishburn_superset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfFishburnSupersetStrategyproofness():
    """
    Superset-strategyproofness for Fishburn ranking of sets
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                for c1 in allCommittees():
                    k = sum(c1)
                    for c2 in allCommitteesOfSize(k):
                        if strictlyBetter(i, c1, c2, p1):
                            clause1 = [negLiteral(c1, p1), negLiteral(c2, p2), posLiteral(c1, p2)]
                            clause2 = [negLiteral(c1, p1), negLiteral(c2, p2), posLiteral(c2, p1)]
                            cnf.append(clause1)
                            cnf.append(clause2)
    return cnf



@cache("cnf_kelly2_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfKelly2CardinalityStrategyproofness():
    """
    Cardinality-strategyproofness for Kelly ranking of sets
    This is an alternative way of generating the clauses that should be
    equivalent to cnfKellyCardinalityStrategyproofness
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for c1 in allCommittees():
                    k = sum(c1)

                    card = cardinalityOfOverlap(p1[i], c1)
                    for c2 in allCommitteesOfSize(k):
                        if cardinalityOfOverlap(p1[i], c2) > card:
                            clause = [negLiteral(c1, p1), negLiteral(c2, p2)]
                            cnf.append(clause)
    return cnf

@cache("cnf_optim_card_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfOptimisticCardinalityStrategyproofness():
    """
    Cardinality-strategyproofness with respect to optimistic voters
    """
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
    """
    Cardinality-strategyproofness with respect to pessimistic voters
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i,p1):
                for c1 in allCommittees():
                    k = sum(c1)
                    clause = [negLiteral(c1, p1)]
                    card = cardinalityOfOverlap(p1[i], c1)
                    for c2 in allCommitteesOfSize(k):
                        if cardinalityOfOverlap(p1[i], c2) <= card:
                            clause.append(posLiteral(c2, p2))
                    cnf.append(clause)
    return cnf

@cache("cnf_optim_superset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfOptimisticSupersetStrategyproofness():
    """
    Superset-strategyproofness with respect to optimistic voters
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                for c2 in allCommittees():
                    k=sum(c2)
                    clause = [negLiteral(c2, p2)]
                    for c1 in allCommitteesOfSize(k):
                        if not strictlyBetter(i, c1, c2, p1):
                            clause.append(posLiteral(c1, p1))
                    cnf.append(clause)
    return cnf

@cache("cnf_pess_superset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfPessimisticSupersetStrategyproofness():
    """
    Superset-strategyproofness with respect to pessimistic voters
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                for c1 in allCommittees():
                    k = sum(c1)
                    clause = [negLiteral(c1, p1)]
                    for c2 in allCommitteesOfSize(k):
                        if not strictlyBetter(i, c1, c2, p1):
                            clause.append(posLiteral(c2, p2))
                    cnf.append(clause)
    return cnf

@cache("cnf_optim_subset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfOptimisticSubsetStrategyproofness():
    """
    Subset-strategyproofness with respect to optimistic voters

    This corresponds to Peter's strategyproofness, but adapted for optimistic voters in the irresolute case
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                # if i's ballot is not a strict subset, 
                # this axiom does nothing
                if not isSubsetOf(p2[i], p1[i]):
                    continue
                for c2 in allCommittees():
                    k=sum(c2)
                    clause = [negLiteral(c2, p2)]
                    for c1 in allCommitteesOfSize(k):
                        if not strictlyBetter(i, c1, c2, p1):
                            clause.append(posLiteral(c1, p1))
                    cnf.append(clause)
    return cnf

@cache("cnf_pess_subset_stratproof_n{}m{}k0{}k1{}.pickle".format(n,m,k0,k1))
def cnfPessimisticSubsetStrategyproofness():
    """
    Subset-strategyproofness with respect to pessimistic voters

    This corresponds to Peter's strategyproofness, but adapted for pessimistic voters in the irresolute case
    """
    cnf = []
    for p1 in tqdm(list(allProfiles())):
        for i in allVoters():
            for p2 in ivariants(i, p1):
                # if i's ballot is not a strict subset, 
                # this axiom does nothing
                if not isSubsetOf(p2[i], p1[i]):
                    continue
                for c1 in allCommittees():
                    k = sum(c1)
                    clause = [negLiteral(c1, p1)]
                    for c2 in allCommitteesOfSize(k):
                        if not strictlyBetter(i, c1, c2, p1):
                            clause.append(posLiteral(c2, p2))
                    cnf.append(clause)
    return cnf

def cnfWeakParetoEfficiency():
    """
    Don't return a committee if there is another committee where every
    voter gets a superset of their approved candidates in the committee,
    and at least one strict superset
    """
    cnf=[]
    for profile in tqdm(list(allProfiles())):
        for k in ks:
            for committee1 in allCommitteesOfSize(k):
                for committee2 in allCommitteesOfSize(k):
                    if strictlySupersetDominates(profile, committee1, committee2):
                        cnf.append([negLiteral(committee2, profile)])
    return cnf


def cnfParetoEfficiency():
    """
    Cardinality-based pareto, dont give committees that are dominated
    """
    cnf=[]
    for profile in tqdm(list(allProfiles())):
        for k in ks:
            for committee1 in allCommitteesOfSize(k):
                for committee2 in allCommitteesOfSize(k):
                    if strictlyDominates(profile, committee1, committee2):
                        cnf.append([negLiteral(committee2, profile)])
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

def cnfJustifiedRepresentation():
    """
    Enforces justified representation (from the Aziz paper), in irresolute case: all winners must satisfy
    """
    cnf = []
    for p in tqdm(list(allProfiles())):
        for c in allCommittees():
            if not satisfiesJR(c, p):
                cnf.append([negLiteral(c,p)])
    return cnf


def cnfExtendedJustifiedRepresentation():
    """
    In irresolute case: all winners must satisfy
    """#
    cnf = []
    for p in tqdm(list(allProfiles())):
        for c in allCommittees():
            if not satisfiesEJR(c, p):
                cnf.append([negLiteral(c,p)])
    return cnf


def cnfAtLeastOne():
    """
    Every profile should give at least a single winning committee
    """
    cnf = []
    for r in tqdm(list(allProfiles())):
        for k in ks:
            clause = []
            for c in allCommitteesOfSize(k):
                clause.append(posLiteral(c, r))
            cnf.append(clause)
    return cnf


def cnfResolute():
    """
    Every profile should give exactly one winner
    """
    cnf = []
    for r in tqdm(list(allProfiles())):
        for k in ks:
            for c1,c2 in combinations(allCommitteesOfSize(k), 2):
                cnf.append([negLiteral(c1, r), negLiteral(c2, r)])
    return cnf


def cnfCommitteeMonotonicity():
    """
    No candidate should be a part of the committee if k=x, but not k=x+1.
    Largely untested
    """
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


def cnfTiebreakInFavorOfMoreVotes():
    """
    Only allows ties (irresolute) between committees with the same AV score
    """
    cnf = []
    for profile in tqdm(list(allProfiles())):
        for k in ks:
            for committee1 in allCommitteesOfSize(k):
                for committee2 in allCommitteesOfSize(k):
                    if votesForCommittee(profile, committee1) != votesForCommittee(profile, committee2):
                        cnf.append([negLiteral(committee1, profile), negLiteral(committee2, profile)])
    return cnf


# leave this for reasons (specifically, ensuring that 
# literals still mean the same thing for cached results)
cnfAtLeastOne()


def broad_test(axiom_list, outputfilepath="testresults.txt"):
    """
    Tests every combination of axioms in a cnf-like format (which seemed appropriate). Input format as follows:

    axiom_list is an iterable (generally a list) of lists, in 
    which every element is a function which returns the cnf for 
    an axiom. Every sublist indicates that one of the axioms within it must be a part of every trial. Thus, a singleton is a 
    necessary part (which is for example generally appropriate 
    for atLeastOne).

    Duplicate axioms within a trial as well as duplicate trials are 
    removed efficiently, so the encoding need not prevent duplicates.
    """
    # get every single axiom used (without duplicates)
    all_used_axioms = set()
    for sublist in axiom_list:
        for ax in sublist:
            all_used_axioms.add(ax)

    # map every axiom to an integer
    ax2int = {}
    int2ax = {}
    for i,ax in enumerate(all_used_axioms):
        ax2int[ax] = i
        int2ax[i] = ax
    # map integers to corresponding cnfs 
    # allows us to only calculate them once
    print("Gathering all cnf formulas:")
    int2cnf = {}
    for ax, i in ax2int.items():
        print(ax.__name__)
        int2cnf[i] = ax()

    # transform axioms given into ints, for easier duplicate removal
    axiom_list = [[ax2int[ax] for ax in sublist] for sublist in axiom_list]

    # get every trial by taking the cartesian product of input
    trials = product(*axiom_list)
    # remove duplicate axioms per trial
    trials = [tuple(sorted(list(set(x)))) for x in trials]

    # remove duplicate trials
    trials = list(set(trials))
    trials.sort()
    with open(outputfilepath, 'w') as f:
        print("Solving:")
        for trial in tqdm(trials):
            cnf = chain(*[int2cnf[ax] for ax in trial])
            ans = pylgl.solve(cnf)
            if ans == "UNSAT":
                ans = "Unsatisfiable"
            else:
                ans = "Satisfiable  "
            
            axnames = [int2ax[ax].__name__ for ax in trial]
            f.write(f"{ans}: {', '.join(axnames)}\n" )

if __name__ == '__main__':
    
    """
    Indicate here which axioms to use. The test takes the cartesian
    product of sublists and tests all possible unique combinations.
    """

    implemented_axioms = [
        cnfPAV,
        cnfProportionalityVotingRule,
        cnfNeutrality,
        cnfAnonymity,
        cnfStrategyproofness,
        cnfMeanCardinalityStrategyproofness,
        cnfKellyCardinalityStrategyproofness,
        cnfKellySupersetStrategyproofness,
        cnfFishburnSupersetStrategyproofness,
        cnfKelly2CardinalityStrategyproofness,
        cnfOptimisticCardinalityStrategyproofness,
        cnfPessimisticCardinalityStrategyproofness,
        cnfOptimisticSupersetStrategyproofness,
        cnfPessimisticSupersetStrategyproofness,
        cnfOptimisticSubsetStrategyproofness,
        cnfPessimisticSubsetStrategyproofness,
        cnfWeakParetoEfficiency,
        cnfParetoEfficiency,
        cnfProportionality,
        cnfJustifiedRepresentation,
        cnfExtendedJustifiedRepresentation,
        cnfAtLeastOne,
        cnfResolute,
        cnfCommitteeMonotonicity,
        cnfTiebreakInFavorOfMoreVotes
        ]

    axioms = [
        [cnfAtLeastOne],
        [cnfProportionality],
        [cnfParetoEfficiency],
        [cnfOptimisticCardinalityStrategyproofness],
        [cnfPessimisticCardinalityStrategyproofness],
        ]
    
    broad_test(axioms, "result_n4.txt")

    #main_result_cnf = cnfAtLeastOne() + cnfProportionality() + cnfOptimisticSubsetStrategyproofness() + cnfPessimisticSubsetStrategyproofness() + cnfParetoEfficiency()
    #dimacs(main_result_cnf, len([*[cnfAtLeastOne]]), len(main_result_cnf), 'mainresult.dimacs')
