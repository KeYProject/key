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

package de.uka.ilkd.key.util;

import java.io.*;
import java.net.URL;
import java.util.Random;


public final class TipOfTheDay {

    private final static Random r = new Random();
    private final static String[] TIPS = getTips();


    /**
     * Randomly select a string
     */
    public static String get() {
        return TIPS[r.nextInt(TIPS.length)];
    }

    /**
     * Read strings from file
     */
    private static String[] getTips() {
        String res = "";
        try {
            final KeYResourceManager krm = KeYResourceManager.getManager();
            final URL tipsUrl = krm.getResourceFile(TipOfTheDay.class, "tipsOfTheDay");
            final InputStream is = new BufferedInputStream(tipsUrl.openStream());
            int c;
            while ((c=is.read()) !=-1) {
                res += (char)c;
            }
            is.close();
            return res.split("\n");
        } catch (IOException e) {
            return new String[]{""};
        }
    }

}