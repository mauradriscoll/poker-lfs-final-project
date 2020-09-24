# poker-lfs-final-project
A simulation of a poker game, run using Forge (a declarative modeling language similar to alloy)

POKER: FORGE STYLE

DESIGN DETAILS :

The goal of our project was to model a simplified game of Texas Hold 'Em Poker using
Forge as a way of modeling the different states of the game, as well as utilizing randomness 
to determine when players go in and out of the game. Our original target goal included a full 
deck of cards, betting with chips, and players deciding their best hand of 5 out of 7 cards 
total. However, after discussing with our TA, we had to make concessions for the sake of speed 
and memory in addition to other limitations in Forge. For example, determining a player's best 
hand would have been overly-complicated and having a betting based on probability of winning 
was not suitable for Forge. We included the following concessions, although we were able to 
incorporate strategy components with a "SmartPlayer" Sig that employs a certain strategy in 
order to view how successful they are.

Our simplified game of Poker has the follow properties:
- 15 cards instead of 52 for memory considerations and also
to make the game more interesting. In this way, there are more chances
to get higher scoring Poker hands.
- The 15 Cards are made up of 5 values (10, Jack, Queen, King, Ace) and 
3 suites (Clubs, Diamonds, and Hearts)
- Instead of having a 5-card flop (shared pot) and 2-card hands, we decided the flop should 
only be 3 cards so that a player’s hand is predetermined. In this way, we can avoid the complicated 
strategy of calculating a player’s best hand, which would be extremely slow and take up a lot of memory. 
- The hands that we are able to represent include: Royal Flush (a regular Flush is a Royal Flush 
in our deck), Full House, Straight, Three of a Kind, Two Pair, and Pair
- The concept of folding (leaving the game) is random, and thus, we just have very elementary 
Poker players. We ensured that when a player leaves in between rounds randomly, they cannot 
come back in and join a subsequent round.
-We maintain that there is always at least one player still remaining in the game at the end, 
so that there must be a Winner.
- If specified, one can play the game with a "SmartPlayer" who employs a strategy laid out
in certain predicates.

We also decided to make setting up the deck an instance because it is much faster than using 
“sing” in the declaration of a predicate that sets up the deck. Therefore, instead of including 
the deck set up in the setUp pred, we run an instance with “for setUpDeck”.


SIGS:

Suite:
- has the three suite sigs extending from it (Hearts, Clubs, Spades)

Card: 
- has an integer value representing the card value (1 is 10, 2 is Jack, etc.)
- has a suite property representing one Suite: Hearts, Clubs, or Spades
- each of the 15 Cards is its own Sig

Player:
- has a set of two cards that they maintain throughout the duration of the game
-score property is used to calculate the player with the best score in the last state 
(StateD). This is only update in the last state
- SmartPlayer: essentially a placeholder if a strategy wants to be used, if not, then 
add 0 SmartPlayer to the run statement

State:
- inPlayers: a set of Player that are still in the game (have not folded) and are 
currently eligible to win
- outPlayers: a set of Players who are out of the game (folded) during some transition
- flop: the cards that are shared by all players to create a hand
- winner: is empty for all of the States expect the last, where the winner(s) is chosen
based on their score that is calculated in the last state
- winningScore: the score of the winning hand in the last state


INSTANCES:

Each instance in Forge is meant to represent one round of a poker game:
- There are 5 Players, each player has a hand (set of 2 cards) that they maintain through each 
round in the game. 
- The initial state contains each player with their random 2 cards, and no cards on the table. 
- The next State (StateB) includes a new card on the table, and during this transition from Initial 
to StateB, we allow Forge to randomly choose the players that to go out of the inPlayers set and 
into the outPlayers set (which represents folding).
- The next State (StateC) has 2 cards down on the table, and in the transition from StateB to 
StateC, players in the inPlayers set can be chosen to randomly go out, but the players in the 
outPlayers set cannot come back in.
- The last transition from StateC to StateD allows players in the inPlayers set to go out one 
last time and the final card is put on the table. Then, in StateD, every player's hand is 
evaluated for its score using predicates for each type of poker hand. After each player is 
scored, the player(s) with the highest score is in the winner set in StateD and their score 
is the winningScore. 

***
One convenient feature of Forge for scoring was being able to utilize joins. For example, to see 
if a player has a Flush, you can use “one hand.suite” because joining the Card in their hand on 
the suite set should only produce a set with one value. Similarly, with a straight you can check
 that the size of the set “hand.value” is 5 because the hand should include all 5 values. This 
 saves having to code with quantification.
***

CHECKS AND VERIFICATIONS:

Verifications: 

Summary:
The first section of testing in our forge file, titled accuracy-checking preds, verifies that 
important structural properties of a poker game are preserved in our model. Although our model 
is a simplification of a poker game—with a smaller deck and minimum betting functionality for 
memory minimization purposes—properties like the player with the best hand wins should be preserved.

Details of each verification pred:
best_hand_wins_verification: 
- the winning score is the score of the players in the StateD.winner set, and if a player is not 
in StateD.winner their score is not the winning score

outPlayer_cant_Win:
- a player in the outPlayer set (ie they have folded) cannot win the game

inPlayer_outPlayer_Verification:
- once a player is in the outPlayer set they stay there for the duration of the game. You cannot 
fold and then come back into the game
- a player in the inPlayer set has been in the inPlayer set for all previous states of the 
game. 

always_some_inPlayer:
- there must be some players still playing at the end of the game. 

cardGame_Properties:
- each player has two cards, and the flop (shared pot of cards) gains one additional card at
each state. It starts with 0 cards in StateA and ends with 3 cards in StateD. 

scoring_properties:
- checks that hands are properly scored; if a player has a score they have the hand that 
corresponds with that score. 
- also checks that hands are scored as the highest possible hand; for example, if a player
is scored for having a straight, they do not have a flush. 

best_hand:
- checks that no player still in the game in the final state had a better hand than the 
winning hand. This ensures that the winning hand is the best hand in the game in the 
final round. 

Instance Testing:

Summary:
Instance Testing was useful in verifying the accuracy of our model because we could set up 
specific hands and make sure that they are detected properly. We were also able to make sure 
these hands were properly scored, winners were properly chosen, and the inPlayer and outPlayer 
sets were distinct and functional. 

Details of Each Instance:
Deck_setup_inst:
- this sets up the cards and states as instances for use in the specific game-like instances below. 

one_inPlayer:
- this instance checks that a game with only one player left in StateD.inPlayer is satisfiable. 
The Player that is left in the inPlayer set wins the game. Their hand is a Royal Flush, it is 
detected and scored properly. 

Royal_flush_wins:
- This instance checks that a player with a royal flush wins the game against players with pairs.

Royal_flush_wins_2:
- This instance checks that a player with a royal flush wins the game against players with straights
 and 3 of a kind. 

Three_of_kind_wins:
- This instance checks that a player with three of a kind wins the game against players with two 
pairs and one pair. 

Two_pair_wins:
- This instance checks that a player with two pairs beats a player with one pair. 

Full_house_wins:
- This instance checks that a full house beats two pairs. 

No_players_left:
- This instance checks that a game with no StateD.inPlayer is unsatisfiable. 

MORE ABOUT STRATEGY COMPONENTS:

We have implemented two potential strategies for the game to make more interesting instances and 
a more realistic game. One strategy (running testStrategyPair) would produce one SmartPlayer who 
only stays in the game only if they have a pair in their hand. We compared this strategy to a strategy 
where a player stays in only if they have a three of a kind with the first card in the flop (running 
testStrategyThree). We noticed qualitatively while scrolling through instances that the player with 
the Three of a Kind strategy wins more often when they remain in the game, however, they fold more 
often than the player with the pair. Thus, from obersvation we found the pair strategy more effective. 
A possible extension of this project could be creating something to count the number of instances 
where each type of smart player wins or loses in the final round. 
We also tested two strategies where a player stays in to the end if they have a flush within the first three 
cards (their 2 cards + first card in the flop) and a player stays in with a flush in the first 
4 cards. Compared to the pair strategy we found this strategy less effective because the player 
going for a flush folds more often and has more varied cards so there is less of a chance of three 
of a kind, a two pair or a full house. However, there is a greater chance for a royal flush or 
straight so when these Smart Players with a flush strategy win, they win with higher scores. 
