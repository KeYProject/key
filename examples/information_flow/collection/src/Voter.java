
import java.io.IOException;

/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 *
 * @author christoph
 */
public class Voter {
    public static int low_outputStream;
    public static boolean low_outputStreamAvailable;
    private static int high_inputStream;

    public static final int low_NUM_OF_VOTERS = 763;
    public static int low_numOfVotes;
    public boolean low_sendSuccessful;
    
    private boolean high_voteValid;
    
    /*@ respects low_outputStream,
                 low_outputStreamAvailable,
                 low_NUM_OF_VOTERS,
                 low_numOfVotes,
                 low_sendSuccessful;    @*/
    void secure_voting() {
        int high_vote = inputVote();
        if (isValid(high_vote)) {
            high_voteValid = true;
            low_sendSuccessful = sendVote(high_vote);
        } else {
            high_voteValid = false;
            low_sendSuccessful = sendVote(0);
        }
        low_numOfVotes = (low_sendSuccessful ? low_numOfVotes + 1 : low_numOfVotes);
        publishVoterParticipation();
    }
    
    /*@ respects low_outputStream,
                 low_outputStreamAvailable,
                 low_NUM_OF_VOTERS,
                 low_numOfVotes,
                 low_sendSuccessful;    @*/
    int inputVote() {
        return high_inputStream;
    }
    
    /*@ respects low_outputStream,
                 low_outputStreamAvailable,
                 low_NUM_OF_VOTERS,
                 low_numOfVotes,
                 low_sendSuccessful,
                 \result;               @*/
    boolean sendVote(int x) {
        if (low_outputStreamAvailable) {
            // encrypt and send over some channel (not further modeled here)
            return true;
        } else {
            return false;
        }
    }
    
    /*@ respects low_outputStream,
                 low_outputStreamAvailable,
                 low_NUM_OF_VOTERS,
                 low_numOfVotes,
                 low_sendSuccessful;    @*/
    boolean isValid(int high_vote) {
        // vote has to be in range 1..255
        return 0 < high_vote && high_vote <= 255;
    }
    
    /*@ respects low_outputStream,
                 low_outputStreamAvailable,
                 low_NUM_OF_VOTERS,
                 low_numOfVotes,
                 low_sendSuccessful;    @*/
    void publishVoterParticipation() {
        low_outputStream = low_numOfVotes * 100 / low_NUM_OF_VOTERS;
    }
    
    
    /*@ respects low_outputStream,
                 low_outputStreamAvailable,
                 low_NUM_OF_VOTERS,
                 low_numOfVotes,
                 low_sendSuccessful;    @*/
    void insecure_voting() {
        int high_vote = inputVote();
        // vote has to be in range 1..255
        if (0 < high_vote && high_vote <= 255) {
            low_sendSuccessful = sendVote(high_vote);
            low_numOfVotes++;
        } else {
            high_vote = 0;
            low_sendSuccessful = sendVote(high_vote);
        }
        publishVoterParticipation();
    }
}
