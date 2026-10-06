/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.rules;


/// @author jomi
/// This Exception signals the abort of a rule Application
public class RuleAbortException extends RuntimeException {
    public RuleAbortException() {
        super("A rule application has been aborted");
    }

    public RuleAbortException(String msg) {
        super(msg);
    }

}
