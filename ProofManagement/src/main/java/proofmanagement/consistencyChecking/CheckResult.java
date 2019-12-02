package proofmanagement.consistencyChecking;

import java.util.ArrayList;
import java.util.List;

/**
 * This class serves as a container for the data returned by a Checker.
 */
public class CheckResult {
    private boolean consistent = false;

    // types of message: [INFO], [ERROR], [WARNING], [RESULT]
    private List<String> messages = new ArrayList<>();

    public CheckResult(boolean consistent) {
        this.consistent = consistent;
    }

    public void addMessage(String message) {
        messages.add(message);
    }

    public void addMessages(List<String> otherMessages) {
        messages.addAll(otherMessages);
    }

    public boolean isConsistent() {
        return consistent;
    }

    public List<String> getMessages() {
        return messages;
    }

    public CheckResult join(CheckResult other) {
        CheckResult res = new CheckResult(other.isConsistent() && isConsistent());
        res.addMessages(this.getMessages());
        res.addMessages(other.getMessages());
        return res;
    }
}
