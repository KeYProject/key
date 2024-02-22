/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

/**
 * Very simple sample implementation for a rule which matches certain strings.
 */
public class IdentifierRule implements MixFixRule<String, String> {

    @Override
    public boolean isLeftRecursive() {
        return false;
    }

    @Override
    public ADTList<ParseContext<String, String>> parse(
            ParseContext<String, String> context, int minBinding) {

        DebugLog.enter(context, minBinding);

        String t = context.getCurrentToken();
        if(t.matches("[a-z]+")) {
            context = context.consumeToken();
            context = context.setResult(t);
            DebugLog.leave(context);
            return ADTList.singleton(context);
        } else {
            DebugLog.leave("nil");
            return ADTList.nil();
        }
    }

}
