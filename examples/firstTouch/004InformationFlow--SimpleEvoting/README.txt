Information flow example.

The example is a simplified version of an evoting case-study that we are investigating in cooperation with the group of Ralf Küsters at the University of Trier. This version has already been verified with KeY, the information flow part as well as the functional part.

Voters send their secrete votes (encrypted, but this not modeled throughout in this version) over a channel (for instance the internet) to a server. The server counts the votes for the different parties. After all voters voted, the result of the election is published. The order in which voters vote (and whether a voter votes at all) is decided by an adversary which is able to control the channel. The result of the election is declassified.

The difficult part in this case-study is to show that indeed only the correct result of the election is declassified.


--- source code ---

public final class Setup {

    private /*@ spec_public @*/ static Voter[] voters;
    private /*@ spec_public @*/ static Server server;
    private /*@ spec_public @*/ static int numberOfVoters;
    private /*@ spec_public @*/ static int numberOfCandidates;

    private /*@ spec_public nullable */ static int[] out;


    /*@ invariant \nonnullelements(voters);
      @ invariant server != null && \invariant_for(server);
      @ invariant voters.length == numberOfVoters;
      @ invariant (\forall int i; 0 <= i && i < voters.length; voters[i].id == i);
      @ invariant (\forall int i; 0 <= i && i < voters.length; \invariant_for(voters[i]));
      @ accessible \inv: numberOfVoters, numberOfCandidates,
      @                  server, server.rep, voters, voters.*,
      @                  \infinite_union(int i; (0 <= i && i < voters.length) ? voters[i].* : \empty);
      @*/

    /*@ normal_behavior
      @ requires (\forall int j; 0 <= j && j < numberOfVoters; !server.ballotCast[j]);
      @ requires (\forall int i; 0 <= i && i < numberOfCandidates; server.votesForCandidates[i]==0);
      @ ensures (\forall int i; 0 <= i && i < numberOfCandidates;
      @              server.votesForCandidates[i] ==
      @                  (\num_of int j; 0 <= j && j < numberOfVoters; voters[j].vote == i));
      @ diverges true;
      @ assignable  server.ballotCast[*], server.votesForCandidates[*],
      @             Environment.rep, out;
      @ determines  Environment.result \by Environment.result, numberOfVoters;
      @ determines  out, (\seq_def int i; 0; out.length; out[i])
      @        \by  numberOfCandidates, numberOfVoters, server.votesForCandidates
      @             \declassifies (\seq_def int i; 0; numberOfCandidates;
      @                               (\num_of int j; 0 <= j && j < numberOfVoters; voters[j].vote == i));
      @*/
    public void main () {
        boolean resultReady = server.resultReady();
        /*@ maintaining \invariant_for(this);
          @
          @   // votes for candidates are sums from voters already voted
          @ maintaining (\forall int i; 0 <= i && i < numberOfCandidates;
          @                  server.votesForCandidates[i] ==
          @                      (\num_of int j; 0 <= j && j < numberOfVoters; server.ballotCast[j] && voters[j].vote == i));
          @
          @ maintaining resultReady == (\forall int j; 0 <= j && j < numberOfVoters; server.ballotCast[j]);
          @
          @ assignable server.ballotCast[*], server.votesForCandidates[*],
          @            Environment.rep;
          @ determines Environment.result, resultReady, numberOfVoters,
          @            (\seq_def int i; 0; numberOfVoters; server.ballotCast[i])
          @        \by \itself;
          @*/
        while ( !resultReady ) { // possibly infinite loop
            // let adversary decide send order
            final int k = Environment.untrustedInput(voters.length);
            final Voter v = voters[k];
            v.onSendBallot(server);
            resultReady = server.resultReady();
        }
        publishResult();
    }


    /*@ normal_behavior
      @ requires (\forall int i; 0 <= i && i < numberOfCandidates;
      @              server.votesForCandidates[i] ==
      @                  (\num_of int j; 0 <= j && j < numberOfVoters; voters[j].vote == i));
      @ assignable out;
      @ determines  out, (\seq_def int i; 0; out.length; out[i])
      @        \by  numberOfCandidates, numberOfVoters, server.votesForCandidates
      @             \declassifies (\seq_def int i; 0; numberOfCandidates;
      @                               (\num_of int j; 0 <= j && j < numberOfVoters; voters[j].vote == i));
      @*/
    private void publishResult () {
        out = server.votesForCandidates;
    }

}


public final class Server {

    public final int numberOfVoters;
    public final int numberOfCandidates;
    private /*@ spec_public @*/ final boolean[] ballotCast;  // ballotCast[i]==true iff the i-th voter has already cast her ballot
    /*@ spec_public @*/ final int[] votesForCandidates;


    Server (int n, int m) {
        //@ set rep = \set_union(\all_fields(this), \set_union(\singleton(Setup.numberOfVoters), \singleton(Setup.numberOfCandidates)));
        numberOfVoters = n;
        numberOfCandidates = m;
        ballotCast = new boolean[n];
        votesForCandidates = new int[m];
    }

    /*@ public invariant numberOfVoters == Setup.numberOfVoters;
      @ public invariant numberOfCandidates == Setup.numberOfCandidates;
      @ public invariant ballotCast.length == numberOfVoters;
      @ public invariant votesForCandidates.length == numberOfCandidates;
      @
      @ public ghost \locset rep;
      @ public invariant rep ==
      @     \set_union( this.*, \locset( Setup.numberOfVoters,
      @                                  Setup.numberOfCandidates ) );
      @
      @ accessible \inv: rep;
      @*/


    /**
     * Collects and counts one single ballot.
     */
    /*@ normal_behavior
      @ requires \invariant_for(msg);
      @ requires 0 <= msg.id && msg.id < numberOfVoters;
      @ requires 0 <= msg.ballot && msg.ballot < numberOfCandidates;
      @ requires ! ballotCast[msg.id];
      @ ensures votesForCandidates[msg.ballot] == \old(votesForCandidates[msg.ballot])+1;
      @ ensures ballotCast[msg.id];
      @ assignable votesForCandidates[msg.ballot], ballotCast[msg.id];
      @
      @ also 
      @
      @ normal_behavior
      @ requires \invariant_for(msg);
      @ requires 0 <= msg.id && msg.id < numberOfVoters;
      @ requires ballotCast[msg.id];
      @ assignable \strictly_nothing;
      @*/
    public void onCollectBallot(Message msg) {
        if (msg == null) return;
        int voterID = msg.id;
        int voteFor = msg.ballot;
        if( voterID<0 || voterID>=numberOfVoters ) return;  // invalid  voter ID
        if( ballotCast[voterID] ) return;  // the voter has already voted
        ballotCast[voterID] = true;
        if (voteFor < 0 || voteFor >= numberOfCandidates ) return;
        else votesForCandidates[voteFor]++;
    }

    /*@ normal_behavior
      @ ensures true;
      @*/
    public /*@ strictly_pure @*/ void onSendResult() {
        final int[] result = getResult();
        // do nothing yet
    }


    /**
     * Returns true if the result is ready, that is if all the eligible voters have already voted.
     */
    /*@ normal_behavior
      @ ensures \result == (\forall int j; 0 <= j && j < numberOfVoters; ballotCast[j]);
      @ accessible rep, ballotCast.*;
      @*/
    public /*@ strictly_pure @*/ boolean resultReady() {
        /*@ loop_invariant 0 <= i && i <= numberOfVoters;
          @ loop_invariant (\forall int j; 0 <= j && j < i; ballotCast[j]);
          @ assignable  \strictly_nothing;
          @ decreases   numberOfVoters-i;
          @*/
        for( int i=0; i<numberOfVoters; i++ ) {
            if( !ballotCast[i] )
                return false;
        }
        return true;
    }

    private /*@ strictly_pure nullable @*/ int[] getResult() {
        if (resultReady())
            return votesForCandidates;
        else return null;
    }
}


public final class Voter {

    private /*@ spec_public @*/ final int id;
    /*@ spec_public @*/ final int vote;


    Voter (int id, int vote) {
        this.id = id;
        this.vote = vote;
    }

    /*@ public invariant 0 <= vote && vote < Setup.numberOfCandidates;
      @ public invariant 0 <= id && id < Setup.numberOfVoters;
      @ accessible \inv: this.*, Setup.numberOfCandidates,
      @                  Setup.numberOfVoters;
      @*/


    /*@ normal_behavior
      @ requires ! server.ballotCast[id];
      @ requires \invariant_for(server);
      @ ensures server.votesForCandidates[vote] == \old(server.votesForCandidates[vote])+1;
      @ ensures server.ballotCast[id];
      @ assignable server.votesForCandidates[vote], server.ballotCast[id],
      @            Environment.rep;
      @ determines Environment.result \by \itself;
      @ also normal_behavior
      @ requires server.ballotCast[id];
      @ requires \invariant_for(server);
      @ ensures  \old(server.votesForCandidates[vote]) == server.votesForCandidates[vote];
      @ ensures  \old(server.ballotCast[id]) == server.ballotCast[id];
      @ assignable Environment.rep;
      @ determines Environment.result \by \itself;
      @*/
    public void onSendBallot(Server server) {
        Message message = new Message(id, vote);
        //@ set message.source = this;
        SMT.send(message, id, server);
    }
}


public final class Message {

    public final int id;
    public final int ballot;
    //@ public ghost Voter source;

    //@ public invariant source.id == id;
    //@ public invariant 0 <= id && id < Setup.numberOfVoters;
    //@ accessible \inv : this.*, Setup.numberOfVoters, source.id;

    public Message (int id, int ballot) {
        this.ballot = ballot;
        this.id = id;
    }

}


public final class SMT {


    /*@ normal_behavior
      @ requires \invariant_for(msg);
      @ requires 0 <= msg.id && msg.id < server.numberOfVoters;
      @ requires 0 <= msg.ballot && msg.ballot < server.numberOfCandidates;
      @ requires ! server.ballotCast[msg.id];
      @ requires \invariant_for(server);
      @ ensures server.votesForCandidates[msg.ballot] == \old(server.votesForCandidates[msg.ballot])+1;
      @ ensures server.ballotCast[msg.id];
      @ assignable server.votesForCandidates[msg.ballot], server.ballotCast[msg.id],
      @            Environment.rep;
      @ determines Environment.result \by \itself;
      @
      @ also
      @
      @ normal_behavior
      @ requires \invariant_for(msg);
      @ requires 0 <= msg.id && msg.id < server.numberOfVoters;
      @ requires server.ballotCast[msg.id];
      @ requires \invariant_for(server);
      @ assignable Environment.rep;
      @ determines Environment.result \by \itself;
      @*/
    //@ helper
    public static void send(Message msg,
                     int senderID,
                     Server server) {
        byte[] output_message =
                SMTEnv.send(/*msg.length*/1, /*senderID*/ 0, /*recipient.ID*/ 0, server, /*port*/ 0);
        server.onCollectBallot(msg);
        NetworkClient.send(output_message, server, /*port*/ 0);
    }
}


public class NetworkClient {

    /*@ normal_behavior
      @ ensures     true;
      @ assignable  Environment.rep;
      @ determines  Environment.result, port,
      @             message,
      @             ( (message != null) ? (\seq_def int i; 0; message.length; message[i]) : null )
      @        \by  \itself;
      @*/
    //@ helper
    public static void send(/*@ nullable */ byte[] message,
                            Server server,
                            int port) {
        // input
        Environment.untrustedOutput(0x2301);
        Environment.untrustedOutputMessage(message);
//        Environment.untrustedOutputString(server);
        Environment.untrustedOutput(port);
        // output
//		if ( Environment.untrustedInput()==0 ) throw new NetworkError();
    }
}


public class SMTEnv {

    /*@ normal_behavior
      @ ensures     true;
      @ assignable  Environment.rep;
      @ determines  Environment.result, message_length, sender_id, recipient_id,
      @             port, \result,
      @             ( (\result != null) ? (\seq_def int i; 0; \result.length; \result[i]) : null )
      @       \by   \itself;
      @*/
    //@ helper
    public static /*@ nullable */ byte[] send(int message_length,
                                                           int sender_id,
                                                           int recipient_id,
                                                           Server server,
                                                           int port) {
        Environment.untrustedOutput(7803);
        Environment.untrustedOutput(message_length);
        Environment.untrustedOutput(sender_id);
        Environment.untrustedOutput(recipient_id);
//		Environment.untrustedOutputString(server);
        Environment.untrustedOutput(port);
        return Environment.untrustedInputMessage();
    }
}


public class Environment {

    private /*@ spec_public */ static boolean result; // the LOW variable


    //@ public static model \locset rep;
    //@ public static represents rep = \locset(result);
    //@ accessible rep : \locset(result);
    
    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep;
      @ determines  Environment.result, \result \by Environment.result;
      @*/
    //@ helper
    public static int untrustedInput() {
        // under specified
    }
    /*@ normal_behavior
      @ ensures     0 <= \result && \result < x;
      @ assignable  rep;
      @ determines  Environment.result, \result \by Environment.result, x;
      @*/
    //@ helper
    public static int untrustedInput(int x) {
        // under specified
    }

    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep;
      @ determines  Environment.result \by Environment.result, x;
      @*/
    //@ helper
    public static void untrustedOutput(int x) {
        // under specified
    }


    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep;
      @ determines  Environment.result, \result,
      @             ( (\result != null) ? (\seq_def int i; 0; \result.length; \result[i]) : null )
      @        \by  Environment.result;
      @*/
    //@ helper
    public static /*@ nullable */ byte[] untrustedInputMessage() {
        int len = untrustedInput();
        if (len < 0) {
            return null;
        }
        byte[] returnval = null;
        /*@ normal_behavior
          @ requires    len >= 0;
          @ ensures     returnval != null && \fresh(returnval);
          @ ensures     returnval.length == len;
          @ assignable  \nothing;
          @ determines  Environment.result, returnval
          @        \by  Environment.result, len
          @        \new_objects returnval;
          @*/
        { returnval = new byte[len]; }
        return untrustedInputMessage(returnval);
    }


    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep, returnval[*];
      @ determines  Environment.result, \result,
      @             ( (\result != null) ? (\seq_def int i; 0; \result.length; \result[i]) : null )
      @        \by  Environment.result, returnval;
      @*/
    //@ helper
    public static byte[] untrustedInputMessage(byte[] returnval) {
        /*@ loop_invariant 0 <= i && i <= returnval.length;
          @ loop_invariant returnval != null && returnval == \old(returnval);
          @ assignable rep, returnval[*];
          @ decreases returnval.length - i;
          @ determines Environment.result, returnval,
          @            (\seq_def int j; 0; i; returnval[j]), i
          @        \by \itself;
          @*/
        for (int i = 0; i < returnval.length; i++) {
            returnval[i] = (byte) Environment.untrustedInput();
        }
        return returnval;
    }


    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep;
      @ determines  Environment.result
      @        \by  Environment.result, t,
      @             ( (t != null) ? (\seq_def int i; 0; t.length; t[i]) : null );
      @*/
    //@ helper
    public static void untrustedOutputMessage(/*@ nullable */ byte[] t) {
        if (t == null) {
            return;
        }
        untrustedOutput(t.length);
        /*@ loop_invariant 0 <= i && i <= t.length && t != null;
          @ assignable rep;
          @ decreases t.length - i;
          @ determines Environment.result, t, (\seq_def int i; 0; t.length; t[i]), i
          @        \by \itself;
          @*/
        for (int i = 0; i < t.length; i++) {
            untrustedOutput(t[i]);
        }
    }
}
