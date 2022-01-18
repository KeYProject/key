package enumtest.jls;

/*
 * Taken from JLS 3rd edition, pg. 255 
 */

import java.util.*;

public class Card implements Comparable<Card>, java.io.Serializable {
	public enum Rank {
		DEUCE, THREE, FOUR, FIVE, SIX, SEVEN, EIGHT, NINE, TEN, JACK, QUEEN, KING, ACE
	}

	public enum Suit {
		CLUBS, DIAMONDS, HEARTS, SPADES
	}

	private final Rank rank;

	private final Suit suit;

	private Card(Rank rank, Suit suit) {
		if (rank == null || suit == null)
			throw new NullPointerException(rank + ", " + suit);
		this.rank = rank;
		this.suit = suit;
	}

	public Rank rank() {
		return rank;
	}

	public Suit suit() {
		return suit;
	}

	public String toString() {
		return rank + " of " + suit;
	}

	// Primary sort on suit, secondary sort on rank
	public int compareTo(Card c) {
		int suitCompare = suit.compareTo(c.suit);
		return (suitCompare != 0 ? suitCompare : rank.compareTo(c.rank));
	}

	private static final List<Card> prototypeDeck = new ArrayList<Card>(52);
	static {
		for (Suit suit : Suit.values())
			for (Rank rank : Rank.values())
				prototypeDeck.add(new Card(rank, suit));
	}

	// Returns a new deck
	public static List<Card> newDeck() {
		return new ArrayList<Card>(prototypeDeck);
	}
}
