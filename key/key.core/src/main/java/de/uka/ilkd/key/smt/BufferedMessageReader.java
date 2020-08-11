// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.proof.mgt.AxiomJustification;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;


/**
 * Wraps BufferedReader in order to provide different message delimiters.
 *
 * It returns successive message which are separated by one of a set of
 * delimiters.
 *
 * For example:
 * <pre>
 *     delims = { "X", "Y" };
 *     br = new BufferedMessageReader(new StringReader("aXbYc"), delims);
 *     assert("a".equals(br.readMessage()));
 *     assert("b".equals(br.readMessage()));
 *     assert("c".equals(br.readMessage()));
 *     assert(null == br.readMessage());
 * </pre>
 *
 * The original implementation would *not* return "c" but return null after
 * b.
 *
 * The method {@link #drain()} can be used to read the reader to the end
 * and give it back as a single string.
 *
 * @author Benjamin Niedermann (original version)
 * @author Mattias Ulbrich (complete overhaul)
 */
class BufferedMessageReader {

	/** the wrapped reader */
	private final Reader reader;

	/** the delimiters supported in this instance */
	private final String[] delimiters;

	public BufferedMessageReader(Reader reader, String[] delimiters) {
		this.reader = reader;
		this.delimiters = delimiters;
	}

	/**
	 * Call this method in order to read the next message from the given input stream. If there is no message,
	 * it blocks until there is a further message or the stream has been closed.
	 * @return a string between two delimiters or until the EOF.
	 * @throws IOException if reading fails
	 */
	public String readMessage() throws IOException {

		StringBuilder sb = new StringBuilder();
		int c;
		while((c = reader.read()) != -1) {
			sb.append((char)c);
			for (String delim : delimiters) {
				if(endsWith(sb, delim)) {
					String result = sb.substring(0, sb.length() - delim.length());

					if(!result.isEmpty()) {
						return result;
					}

					// if empty then continue with an empty buffer
					sb.setLength(0);
				}
			}
		}

        if (sb.length() == 0) {
            // return null to indicate a finished stream
            return null;
        } else {
		return sb.toString();
	}
	}

	/**
	 * This method checks if a character sequence ends with a string.
	 *
	 * Semantically it is equivalent to {@code sb.toString().endsWith(s)}.
	 *
	 * It is more efficient since no arrays must be copied ...
	 *
	 * @param sb any non-null character sequence
	 * @param s the non-null string to check for
	 * @return true if sb ends in s.
	 */
	private static boolean endsWith(CharSequence sb, String s) {
		int len = sb.length();
		int dlen = s.length();

		if (len < dlen) {
			return false;
		}

		for (int i = len - dlen, j = 0; i < len; i++, j++) {
			if(sb.charAt(i) != s.charAt(j)) {
				return false;
			}
		}

		return true;
	}

	/**
	 * Return the remainder of the reader's content as a String.
	 *
	 * The reader is read until its EOF.
	 *
	 * @return a string containing all text (including delimiters)
	 * @throws IOException if reading fails
	 */
	public String drain() throws IOException {
	    char[] buf = new char[1024];
        StringBuilder result = new StringBuilder();
        int len = reader.read(buf);
        while (len >= 0) {
            result.append(buf, 0, len);
            len = reader.read(buf);
        }
        return result.toString();
	}


}