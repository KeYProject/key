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
import de.uka.ilkd.key.util.net.NetworkUtils;


public final class TipOfTheDay {

    private final static boolean USE_INTERNET = true;
    private final static Random r = new Random();
    private final static String[] TIPS = getTips(USE_INTERNET);


    /**
     * Randomly select a string
     */
    public static String get() {
        return TIPS[r.nextInt(TIPS.length)];
    }

    /**
     * Read strings from file and the internet.
     * @param online whether to read from the internet
     */
    private static String[] getTips(boolean online) {
        try {
            String[] res = getTipsFromFile();
            if (online) {
                res = MiscTools.concat(res, getTipsOnline());
            }
            return res;
        } catch (IOException e) {
            return new String[]{""};
        }
    }

    private static String[] getTipsFromFile() throws IOException {
        String res = "";
        final KeYResourceManager krm = KeYResourceManager.getManager();
        final URL tipsUrl = krm.getResourceFile(TipOfTheDay.class, "tipsOfTheDay");
        final InputStream is = new BufferedInputStream(tipsUrl.openStream());
        int c;
        while ((c=is.read()) !=-1) {
            res += (char)c;
        }
        is.close();
        return res.split("\n");
    }
    
    private static String[] getTipsOnline() throws IOException {
        return new String[]{checkLatestVersion()};
    }
    
    private static String checkLatestVersion() {
        final String latestVersion = NetworkUtils.getLatestVersion();
        final String currentVersion = KeYResourceManager.getManager().getVersion();
        final VersionStringComparator vsc = new VersionStringComparator();
        final boolean versionOK = vsc.compare(currentVersion, latestVersion) < 0;
        if (versionOK) return "You are using an up-to-date version of KeY; good for you.";
        else return "It seems that you are using an old version of KeY. The current stable version is "+latestVersion;
    }

}