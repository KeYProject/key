package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.rusty.Services;
import org.key_project.rusty.rule.MatchConditions;

/**
 * Interface that has to be implemented by instructions for the matching virtual machine
 */
public interface MatchInstruction {
    MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
                          Services services);
}
