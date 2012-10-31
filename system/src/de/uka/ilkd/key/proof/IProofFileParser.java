package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.parser.KeYParser;

/**
 * Defines the required which a {@link KeYParser} needs to parse a *.proof
 * file and to apply the reules again. 
 * @author Martin Hentschel
 */
public interface IProofFileParser {
   void beginExpr(char eid, String str);

   void endExpr(char eid, int stringLiteralLine);
}
