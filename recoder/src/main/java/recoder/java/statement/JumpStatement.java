// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.statement;

/**
 * Jump statement.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class JumpStatement extends JavaStatement {

    /**
     * Jump statement.
     */

    public JumpStatement() {
        // nothing to do
    }

    /**
     * Jump statement.
     *
     * @param proto a jump statement.
     */

    protected JumpStatement(JumpStatement proto) {
        super(proto);
    }
}
