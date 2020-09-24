#lang forge

--------SIGS-----------
-- 1 = 10, 2 = Jack, 3 = Queen, 4 = King, 5 = Ace
-- suite is one of Clubs, Spades, Hearts
sig Card {
    value: one Int,
    suite: one Suite
}


--REPRESENTS EACH TYPE OF CARD
one sig TenofS extends Card {}
one sig TenofH extends Card {}
one sig TenofC extends Card {}
one sig JofS extends Card {}
one sig JofH extends Card {}
one sig JofC extends Card {}
one sig QofS extends Card {}
one sig QofH extends Card {}
one sig QofC extends Card {}
one sig KofS extends Card {}
one sig KofH extends Card {}
one sig KofC extends Card {}
one sig AofS extends Card {}
one sig AofH extends Card {}
one sig AofC extends Card {}

--sig to represent the suite of the Card
sig Suite{} 
one sig Hearts extends Suite{}
one sig Clubs extends Suite{}
one sig Spades extends Suite{}

--sig to represent a player in the round, each set of cards is 2
--score is calculated in StateD
sig Player {
    hand: set Card,
    score : one Int
}
--keeps track of the players (if any) who have a strategy
sig SmartPlayer extends Player{}

--A set in players and out players in State because they will change on transition
sig State{
    inPlayers: set Player,
    outPlayers: set Player,
    flop: set Card, --cards open to every player
    winner: set Player, --could be no winner, 1 winner, or a potential tie
    winningScore: lone Int --used to determine who the winner is
}

--States to represent each part of the round
one sig StateA extends State{} 
one sig StateB extends State{} 
one sig StateC extends State{}
one sig StateD extends State{}

pred abstractState { State = StateA + StateB + StateC + StateD}

--setsUpDeck into unique cards
inst setUpDeck{
    Card = TenofS0 + TenofH0+ TenofC0 + JofS0 + JofH0 + JofC0 + QofS0 + QofH0 + QofC0 + KofS0 + KofH0 + KofC0 + AofS0 + AofH0 + AofC0
    Suite = Spades0 + Clubs0 + Hearts0
    value = TenofS0->1 + TenofH0->1 +TenofC0->1 +JofS0->2 + JofH0->2 + JofC0->2 + QofS0->3 + QofH0->3 + QofC0->3 + KofS0->4 + KofH0->4 + KofC0->4 + AofS0->5 + AofH0->5 + AofC0->5
    suite = TenofS0->Spades0 + TenofH0->Hearts0 + TenofC0->Clubs0 + JofS0->Spades0 + JofH0->Hearts0 + JofC0->Clubs0 + QofS0->Spades0 + QofH0->Hearts0 + QofC0->Clubs0 + KofS0->Spades0 + KofH0->Hearts0 + KofC0->Clubs0 + AofS0->Spades0 + AofH0->Hearts0 + AofC0->Clubs0
    
}


------GAME RULE PREDICATES--------------------

/* make sure all cards that are a part of the game are not repeated*/
pred noRepeats {
    --no player can have cards on the table
    all s: State |
        all p : Player |
            no p.hand & s.flop
            
    --no player can have card in another player's hand
    all p: Player|
        all p1: Player|
            p != p1 implies no (p.hand & p1.hand)
}

--every player has two cards
pred playerSetUp{
    all p: Player|
        #p.hand = 2
}

--players cannot be in both in and out sets, but must be in one set------
pred oneSet {
    all s: State|
        all p: Player|
            p in s.outPlayers iff p not in s.inPlayers
            
    --players have to be in one of the sets
    all s: State|
        all p : Player|
            p in s.inPlayers or p in s.outPlayers
}

------CHECKING HAND PREDS------------
--Have all 5 card values
pred Straight[hand : set Card] {
    #(hand.value) = 5
}
--have all one suite (in our game a flush and royal flush are the same)
pred Flush[hand : set Card] {
    one hand.suite
}
--have a three of a kind and pair
pred FullHouse[hand : set Card] {
    --with our deck, the only time there can be only
    --2 distinct values in a hand is when there is a full house
    #(hand.value) = 2

}
--have 3 cards with the same value
pred ThreeOfKind[hand : set Card] {
     #hand.suite = 3
     some c, c1, c2: Card|
                 ((c in hand) and (c1 in hand) and (c2 in hand) and c != c1 and c2 != c and c1 != c2) and
                    c.value = c1.value and c2.value = c1.value and c.value = c2.value

                 
}
--have two sets of two cards with the same value
pred TwoPair[hand : set Card] {
    Pair[hand] and #hand.value = 3
}
--two cards with same values
pred Pair[hand : set Card] {
    some c: Card|
        some c1: Card|
            (c != c1 and c in hand and c1 in hand) and
            c.value = c1.value 
    
}

-------------POSSIBLE STRATEGIES---------------
--if player has a pair in their hand, they stay in
pred smartPlayerPair [p:Player]{
    Pair[p.hand] implies {p in StateD.inPlayers}
        else
        p in StateB.outPlayers
}
--if player has a three of kind with their hand + the flop in StateB, they always stay in
pred smartPlayerThree[p:Player]{
    p in StateB.inPlayers
    ThreeOfKind[p.hand + StateB.flop] implies {p in StateD.inPlayers}
    else
    p in StateC.outPlayers
}

--if player has a flush (3 cards of same suite) with their hand + the flop in StateB, they always stay in
pred smartPlayerFlushThree[p:Player]{
    p in StateB.inPlayers -- 3 cards
    Flush[p.hand + StateB.flop] implies {p in StateD.inPlayers}
    else
    p in StateC.outPlayers
}

--if player has a flush (4 cards of same suite) with their hand + the flop in StateC, they always stay in
pred smartPlayerFlushFour[p:Player]{
    p in StateC.inPlayers -- 4 cards
    Flush[p.hand + StateC.flop] implies {p in StateD.inPlayers}
    else
    p in StateD.outPlayers
}

--test just one smart player with one of the above strategies
pred testStrategyPair{
    one p: Player|
        one SmartPlayer and SmartPlayer = p and
        smartPlayerPair[p]
        
}
--show instances with a smart player who stays in only when they have a three of a kind
pred testStrategyThree{
    one p: Player|
        one SmartPlayer and SmartPlayer = p and
        smartPlayerThree[p]
}

--show instances with a smart player who stays in only when they have a flush of three cards
pred testStrategyFlushThree{
    one p: Player|
        one SmartPlayer and SmartPlayer = p and
        smartPlayerFlushThree[p]
}

--show instances with a smart player who stays in only when he has a flush of four cards
pred testStrategyFlushFour{
    one p: Player|
        one SmartPlayer and SmartPlayer = p and
        smartPlayerFlushFour[p]
}

--tests that a player who stays to the end with a pair beats a player who stays in only with 3 of a kind
pred testStrategyPairBeatsThree{
    #SmartPlayer = 2
    one p: Player|
        one p1: Player|
            SmartPlayer = p + p1  and
            smartPlayerPair[p] and
            p1 != p and smartPlayerThree[p1] and p in StateD.winner and p1 not in StateD.winner
}
--show instances where the player with three of a kind beats a player with a pair in the hand
pred testStrategyThreeBeatsPair{
    #SmartPlayer = 2
    one p: Player|
        one p1: Player|
            SmartPlayer = p + p1  and
            smartPlayerThree[p] and
            p1 != p and smartPlayerPair[p1] and p in StateD.winner and p1 not in StateD.winner
}

--shows instances where a player with the given pair strategy beats the player with the three of a kind strategy
pred testStrategyThreeBeatsPairBothIn{
    #SmartPlayer = 2
    #StateB.outPlayers = 3 --want to eliminate instances where only the other players switch 
    one p: Player|
        one p1: Player|
            SmartPlayer = p + p1  and
            smartPlayerThree[p] and
            p1 != p and
            smartPlayerPair[p1] and
            p in StateD.inPlayers and p1 in StateD.inPlayers and
            p in StateD.winner and p1 not in StateD.winner
}
--shows instances where a player with the given three of a kind strategy beats the player with the pair strategy when both are in StateD
pred testStrategyPairBeatsThreeBothIn{
    #SmartPlayer = 2
    #StateB.outPlayers = 3 --want to eliminate instances where only the other players switch 
    one p: Player|
        one p1: Player|
            SmartPlayer = p + p1  and
            smartPlayerThree[p1] and
            p1 != p and
            smartPlayerPair[p] and
            p in StateD.inPlayers and p1 in StateD.inPlayers and
            p in StateD.winner and p1 not in StateD.winner
}
--tests the two strategies versus each other with no set winner, but controls for the other players
pred testStrategyPairvsThreeBothIn{
    #SmartPlayer = 2
    one p: Player|
        one p1: Player|
            (Player - p - p1) in StateB.outPlayers and--want to eliminate instances where only the other players switch 
            SmartPlayer = p + p1  and
            smartPlayerThree[p1] and
            p1 != p and
            smartPlayerPair[p]
}

--show instances where the player with a flush of 3 beats a player with a flush of 4
pred testStrategyFlushThreeBeatsFlushFour{
    #SmartPlayer = 2
    one p: Player|
        one p1: Player|
            SmartPlayer = p + p1  and
            smartPlayerFlushThree[p] and
            p1 != p and smartPlayerFlushFour[p1] and p in StateD.winner and p1 not in StateD.winner
}
--show instances where the player with a flush of 4 beats a player with a flush of 3
pred testStrategyFlushFourBeatsFlushThree{
    #SmartPlayer = 2
    one p: Player|
        one p1: Player|
            SmartPlayer = p + p1  and
            smartPlayerFlushFour[p] and
            p1 != p and smartPlayerFlushThree[p1] and p in StateD.winner and p1 not in StateD.winner
}
--test a strategy for going for a flush vs having a pair
pred testStrategyPairvsFlushThree{
    #SmartPlayer = 2
    one p: Player|
        one p1: Player|
            SmartPlayer = p + p1  and
            smartPlayerFlushThree[p] and
            p1 != p and smartPlayerPair[p1]
}


--------------------STATES OF THE GAME-----------------------
--pred for starting the game
pred initState {
    #StateA.flop = 0 
    #StateA.outPlayers = 0
    all p: Player | p in StateA.inPlayers
    StateA.winningScore = sing[0]
    #StateA.winner = 0    
}


--intial State to first state (1 card flop)
pred initToFirst{
    initState
    #StateB.flop = 1
    StateB.winningScore = sing[0]
    #StateB.winner = 0  
}
--first state to second state (2 card flop)
pred firstToSecond {
    all p:Player |
        p in StateB.outPlayers implies p in StateC.outPlayers
        
    all c: Card |
        c in StateB.flop implies c in StateC.flop
        
    #StateC.flop = 2
    StateC.winningScore = sing[0]
    #StateC.winner = 0  
}
--second state to final state (3 card flop)
pred secondToThird{
    all p: Player |
        p in StateC.outPlayers implies p in StateD.outPlayers
        
    all c: Card |
        c in StateC.flop implies c in StateD.flop
        
    some StateD.inPlayers
    #StateD.flop = 3

    -- calculates the score for each Player still in the game (in inPlayers set)
    all p: Player |
        --Royal Flush
        (p in StateD.inPlayers and Straight[(p.hand + StateD.flop)] and Flush[(p.hand+StateD.flop)]) implies
        {p.score = sing[15]}
        
        else
        --Full House
        (p in StateD.inPlayers and FullHouse[(p.hand + StateD.flop)]) implies
        {p.score = sing[14]}
        
        else
        --Straight
        (p in StateD.inPlayers and Straight[(p.hand + StateD.flop)]) implies
        {p.score = sing[12]}
        
        else
        --ThreeOfAKind
        (p in StateD.inPlayers and ThreeOfKind[(p.hand + StateD.flop)]) implies
        {p.score = sing[11]}
        
        else
        --TwoPair
        (p in StateD.inPlayers and TwoPair[(p.hand + StateD.flop)]) implies
        {p.score = sing[10]}
        
        else
        --Pair
        (p in StateD.inPlayers and Pair[(p.hand + StateD.flop)]) implies
        {p.score = sing[7]}
-- all players out cannot win and have a score of 0
    all p: Player |
        p in StateD.outPlayers implies {no p & StateD.winner and p.score = sing[0]}
-- find winner by finding max score
    StateD.winningScore = sing[max[Player.score]]
    all p:Player|
        (p.score = StateD.winningScore) implies p in StateD.winner
        else
        (no p & StateD.winner)
        
}

--super pred to set up the game
pred setUp {
    abstractState
    playerSetUp
    noRepeats
    oneSet
    initToFirst
    firstToSecond
    secondToThird
}

--run a game of Poker with all naive players
run {setUp} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int, 0 SmartPlayer for setUpDeck

--replace Pair with Three, FlushThree, or FlushFour
--run {setUp testStrategyPair} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int for setUpDeck

--run {setUp testStrategyPairBeatsThree} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int for setUpDeck

--run {setUp testStrategyThreeBeatsPair} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int for setUpDeck

--run {setUp testStrategyPairBeatsThreeBothIn} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int for setUpDeck

--run {setUp testStrategyThreeBeatsPairBothIn} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int for setUpDeck

--run {setUp testStrategyPairvsThreeBothIn} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int for setUpDeck

--run {setUp testStrategyFlushThreeBeatsFlushFour} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int for setUpDeck

--run {setUp testStrategyFlushFourBeatsFlushThree} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int for setUpDeck

--run {setUp testStrategyPairvsFlushThree} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 6 Int for setUpDeck


--------accuracy-checking preds---------------------------------------------------------------------------------------------------
pred best_hand_wins_verification {
    --the winning score is the score of the player(s) in the StateD.winner set
    all p: Player | (p.score = StateD.winningScore) iff p in StateD.winner
    --if a player is not in the StateD.winner set their score is not the winningScore
    all p: Player | (p.score != StateD.winningScore) iff p not in StateD.winner
}

check {setUp implies best_hand_wins_verification} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 0 SmartPlayer, 6 Int for setUpDeck

pred outPlayer_cant_Win {
    --a player in the outPlayer set cannot win the game
    all p: StateD.outPlayers | no p & StateD.winner
}

check {setUp implies outPlayer_cant_Win} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 0 SmartPlayer, 6 Int for setUpDeck


pred inPlayer_outPlayer_verification {
    --once a player is in the outPlayer set it stays there for the duration of the game
    all p: Player | p in StateA.outPlayers implies p in StateB.outPlayers
    all p: Player | p in StateB.outPlayers implies p in StateC.outPlayers
    all p: Player | p in StateC.outPlayers implies p in StateD.outPlayers
    --a player in the inPlayer set has been in the inPlayer set for the duration of the game
    all p: Player | p in StateD.inPlayers implies p in StateC.inPlayers
    all p: Player | p in StateC.inPlayers implies p in StateB.inPlayers
    all p: Player | p in StateB.inPlayers implies p in StateA.inPlayers
}

check {setUp implies inPlayer_outPlayer_verification}  for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 0 SmartPlayer, 6 Int for setUpDeck

pred always_some_inPlayer {
    --there must be players in the inPlayer set at each state of the game
    some StateA.inPlayers
    some StateB.inPlayers
    some StateC.inPlayers
    some StateD.inPlayers
}

check {setUp implies always_some_inPlayer} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 0 SmartPlayer, 6 Int for setUpDeck

pred cardGame_properties {
    --players all have 2 cards, and the flop has the right amount of cards at each state of the game
    #StateA.flop = 0
    #StateB.flop = 1
    #StateC.flop = 2
    #StateD.flop = 3
    all p: Player | #p.hand = 2
}

check {setUp implies cardGame_properties} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 0 SmartPlayer, 6 Int for setUpDeck

pred scoring_properties {
    --check that hands are properly scored (ie a score implies that that hand exists)
    all p: Player | p.score = sing[7] implies Pair[(p.hand + StateD.flop)]
    all p: Player | p.score = sing[10] implies TwoPair[(p.hand + StateD.flop)]
    all p: Player | p.score = sing[11] implies ThreeOfKind[(p.hand + StateD.flop)]
    all p: Player | p.score = sing[12] implies Straight[(p.hand + StateD.flop)]
    all p: Player | p.score = sing[12] implies not Flush[(p.hand + StateD.flop)]
    all p: Player | p.score = sing[14] implies FullHouse[(p.hand + StateD.flop)]
    all p: Player | p.score = sing[15] implies Flush[(p.hand + StateD.flop)] 
}

check {setUp implies scoring_properties} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 0 SmartPlayer, 6 Int for setUpDeck

pred best_hand {
    --check that no player in StateD.inPlayer had a better hand than the one that corresponds to the winning score
    all p: Player | StateD.winningScore = sing[7] and p in StateD.inPlayers implies not TwoPair[(p.hand + StateD.flop)] and not ThreeOfKind[(p.hand + StateD.flop)] and not Flush[(p.hand+StateD.flop)] and not Straight[(p.hand + StateD.flop)] and not FullHouse[(p.hand + StateD.flop)]
    all p: Player | StateD.winningScore = sing[10] and p in StateD.inPlayers implies not ThreeOfKind[(p.hand + StateD.flop)] and not Flush[(p.hand+StateD.flop)] and not Straight[(p.hand + StateD.flop)] and not FullHouse[(p.hand + StateD.flop)]
    all p: Player | StateD.winningScore = sing[11] and p in StateD.inPlayers implies not Flush[(p.hand+StateD.flop)] and not Straight[(p.hand + StateD.flop)] and not FullHouse[(p.hand + StateD.flop)]
    all p: Player | StateD.winningScore = sing[12] and p in StateD.inPlayers implies not Flush[(p.hand+StateD.flop)] and not FullHouse[(p.hand + StateD.flop)]    
}

check {setUp implies best_hand} for exactly 5 Player, exactly 4 State, exactly 15 Card, exactly 3 Suite, 0 SmartPlayer, 6 Int for setUpDeck

----------instance testing--------------------------------------------------------------------------------------------------------
inst deck_setup_inst {
    --set up the deck as an instance for use in all of the below instance testing
    StateA = StateA0
    StateB = StateB0
    StateC = StateC0
    StateD = StateD0
    Player = Player0 + Player1 + Player2 + Player3 + Player4
    no SmartPlayer
    
    setUpDeck
}
    
inst one_inPlayer {
    --this instance checks that if only one player is in the inPlayer set in the final round, they win
    deck_setup_inst
    
    hand = Player0->KofC0 + Player0->AofH0 + Player1->QofC0 + Player1->KofS0 + Player2->QofH0 + Player2->KofH0 + Player3->JofC0 + Player3->AofC0
      + Player4->TenofS0 + Player4->TenofC0
    score = Player0->7 + Player1->0 + Player2->0 + Player3->0 + Player4->0
    outPlayers = StateD0->Player1 + StateD0->Player2 + StateD0->Player3 + StateD0->Player4
    inPlayers = StateA0->Player0 + StateA0->Player1 + StateA0->Player2 + StateA0->Player3 + StateA0->Player4
                + StateB0->Player0 + StateB0->Player1 + StateB0->Player2 + StateB0->Player3 + StateB0->Player4
                + StateC0->Player0 + StateC0->Player1 + StateC0->Player2 + StateC0->Player3 + StateC0->Player4
                + StateD0->Player0
    flop = StateB0->JofS0 + StateC0->JofS0 + StateC0->QofS0 + StateD0->JofS0 + StateD0->QofS0 + StateD0->AofS0
    winner = StateD0->Player0
    winningScore = StateA0->0 + StateB0->0 + StateC0->0 + StateD0->7
}

inst royal_flush_wins {
    --this instance checks that a royal flush beats players with pairs
    deck_setup_inst
    hand = Player0->KofS0 + Player0->AofS0 + Player1->AofH0 + Player1->AofC0 + Player2->KofH0 + Player2->KofC0 + Player3->QofH0 + Player3->JofH0
           + Player4->TenofH0+ Player4->TenofC0
    score = Player0->15 + Player1->7 + Player2->7 + Player3->0 + Player4->0
    outPlayers = StateD0->Player3 + StateD0->Player4
    inPlayers = StateA0->Player0 + StateA0->Player1 + StateA0->Player2 + StateA0->Player3 + StateA0->Player4
                + StateB0->Player0 + StateB0->Player1 + StateB0->Player2 + StateB0->Player3 + StateB0->Player4
                + StateC0->Player0 + StateC0->Player1 + StateC0->Player2 + StateC0->Player3 + StateC0->Player4
                + StateD0->Player0 + StateD0->Player1 + StateD0->Player2
    flop = StateB0->JofS0 + StateC0->JofS0 + StateC0->QofS0 + StateD0->TenofS0+ StateD0->JofS0 + StateD0->QofS0
    winner = StateD0->Player0
    winningScore = StateA0->0 + StateB0->0 + StateC0->0 + StateD0->15
}

inst royal_flush_wins_2 {
    --this instance checks that a royal flush beats players with straights and 3 of a kind
    deck_setup_inst
    hand = Player0->JofC0 + Player0->TenofC0 + Player1->TenofH0 + Player1->JofH0 + Player2->KofC0 + Player2->KofS0 + Player3->TenofS0 + Player3->AofS0
           + Player4->JofS0 + Player4->AofC0
    score = Player0->12 + Player1->15 + Player2->11 + Player3->0 + Player4->0
    outPlayers = StateD0->Player3 + StateD0->Player4
    inPlayers = StateA0->Player0 + StateA0->Player1 + StateA0->Player2 + StateA0->Player3 + StateA0->Player4
                + StateB0->Player0 + StateB0->Player1 + StateB0->Player2 + StateB0->Player3 + StateB0->Player4
                + StateC0->Player0 + StateC0->Player1 + StateC0->Player2 + StateC0->Player3 + StateC0->Player4
                + StateD0->Player0 + StateD0->Player1 + StateD0->Player2
    flop = StateB0->QofH0 + StateC0->QofH0 + StateC0->KofH0 + StateD0->QofH0+ StateD0->KofH0 + StateD0->AofH0
    winner = StateD0->Player1
    winningScore = StateA0->0 + StateB0->0 + StateC0->0 + StateD0->15
}

inst three_of_kind_wins {
    --This instance checks that a three of a kind beats players with 2 pair and one pair
    deck_setup_inst
    hand = Player0->AofC0 + Player0->JofC0 + Player1->TenofS0 + Player1->JofH0 + Player2->KofC0 + Player2->QofS0 + Player3->QofH0 + Player3->QofC0
           + Player4->TenofC0 + Player4->JofS0
    score = Player0->11 + Player1->10 + Player2->7 + Player3->0 + Player4->0
    outPlayers = StateD0->Player3 + StateD0->Player4
    inPlayers = StateA0->Player0 + StateA0->Player1 + StateA0->Player2 + StateA0->Player3 + StateA0->Player4
                + StateB0->Player0 + StateB0->Player1 + StateB0->Player2 + StateB0->Player3 + StateB0->Player4
                + StateC0->Player0 + StateC0->Player1 + StateC0->Player2 + StateC0->Player3 + StateC0->Player4
                + StateD0->Player0 + StateD0->Player1 + StateD0->Player2
    flop = StateB0->AofH0 + StateC0->AofH0 + StateC0->AofS0 + StateD0->AofH0+ StateD0->AofS0 + StateD0->TenofH0
    winner = StateD0->Player0
    winningScore = StateA0->0 + StateB0->0 + StateC0->0 + StateD0->11
}

inst two_pair_wins {
    --this instance checks that 2 pair beats a single pair
    deck_setup_inst
    hand = Player0->AofC0 + Player0->QofC0 + Player1->TenofS0 + Player1->JofH0 + Player2->KofC0 + Player2->QofS0 + Player3->QofH0 + Player3->JofC0
           + Player4->TenofC0 + Player4->JofS0
    score = Player0->0 + Player1->0 + Player2->0 + Player3->7 + Player4->10
    outPlayers = StateC0->Player0 + StateC0->Player1 + StateD0->Player0 + StateD0->Player1 + StateD0->Player2
    inPlayers = StateA0->Player0 + StateA0->Player1 + StateA0->Player2 + StateA0->Player3 + StateA0->Player4
                + StateB0->Player0 + StateB0->Player1 + StateB0->Player2 + StateB0->Player3 + StateB0->Player4
                + StateC0->Player2 + StateC0->Player3 + StateC0->Player4
                + StateD0->Player3 + StateD0->Player4 
    flop = StateB0->AofH0 + StateC0->AofH0 + StateC0->AofS0 + StateD0->AofH0+ StateD0->AofS0 + StateD0->TenofH0
    winner = StateD0->Player4
    winningScore = StateA0->0 + StateB0->0 + StateC0->0 + StateD0->10
}

inst full_house_wins {
    --this instance checks that a full house beats two pair
    deck_setup_inst
    hand = Player0->AofC0 + Player0->TenofC0 + Player1->TenofS0 + Player1->JofH0 + Player2->KofC0 + Player2->QofS0 + Player3->QofH0 + Player3->QofC0
           + Player4->KofH0 + Player4->JofS0
    score = Player0->14 + Player1->10 + Player2->0 + Player3->0 + Player4->0
    outPlayers = StateD0->Player3 + StateD0->Player4 + StateD0->Player2
    inPlayers = StateA0->Player0 + StateA0->Player1 + StateA0->Player2 + StateA0->Player3 + StateA0->Player4
                + StateB0->Player0 + StateB0->Player1 + StateB0->Player2 + StateB0->Player3 + StateB0->Player4
                + StateC0->Player0 + StateC0->Player1 + StateC0->Player2 + StateC0->Player3 + StateC0->Player4
                + StateD0->Player0 + StateD0->Player1 
    flop = StateB0->AofH0 + StateC0->AofH0 + StateC0->AofS0 + StateD0->AofH0 + StateD0->AofS0 + StateD0->TenofH0
    winner = StateD0->Player0
    winningScore = StateA0->0 + StateB0->0 + StateC0->0 + StateD0->14
}

inst no_players_left {
    --this instance checks that there has to be inPlayers in StateD
    deck_setup_inst
    hand = Player0->AofC0 + Player0->QofC0 + Player1->TenofS0 + Player1->JofH0 + Player2->KofC0 + Player2->QofS0 + Player3->QofH0 + Player3->JofC0
           + Player4->TenofC0 + Player4->JofS0
    score = Player0->0 + Player1->0 + Player2->0 + Player3->0 + Player4->0
    outPlayers = StateC0->Player0 + StateC0->Player1 + StateD0->Player0 + StateD0->Player1 + StateD0->Player2 + StateD0->Player3 + StateD0->Player4 
    inPlayers = StateA0->Player0 + StateA0->Player1 + StateA0->Player2 + StateA0->Player3 + StateA0->Player4
                + StateB0->Player0 + StateB0->Player1 + StateB0->Player2 + StateB0->Player3 + StateB0->Player4
                + StateC0->Player2 + StateC0->Player3 + StateC0->Player4
    flop = StateB0->AofH0 + StateC0->AofH0 + StateC0->AofS0 + StateD0->AofH0+ StateD0->AofS0 + StateD0->TenofH0
    winner = StateD0->Player4
    winningScore = StateA0->0 + StateB0->0 + StateC0->0 + StateD0->0
}

test expect {
    test1: {setUp} for 6 Int for one_inPlayer is sat
    test2: {setUp} for 6 Int for royal_flush_wins is sat
    test3: {setUp} for 6 Int for three_of_kind_wins is sat
    test4: {setUp} for 6 Int for royal_flush_wins_2 is sat
    test5: {setUp} for 6 Int for two_pair_wins is sat
    test6: {setUp} for 6 Int for full_house_wins is sat
    test7: {setUp} for 6 Int for no_players_left is unsat
}
