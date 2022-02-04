// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.

/*
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */

package de.uka.ilkd.key.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 * An infrastructure to read string to string maps from files.
 *
 * Keys are written in form of heading lines like "### key".
 * The values are the lines between headings.
 *
 * This is nice for having larger text blocks to map.
 *
 * @author Mattias Ulbrich
 */
public class LineProperties {

    private Map<String, String> map = new LinkedHashMap<>();

    public void read(InputStream is) throws IOException {
        read(new InputStreamReader(is));
    }

    public void read(Reader reader) throws IOException {
        BufferedReader br = new BufferedReader(reader);

        String line;
        StringBuffer sb = new StringBuffer();
        String lastKey = null;

        while ((line = br.readLine()) != null) {
            if (line.startsWith("###")) {
                if(lastKey != null) {
                    String str = sb.toString().trim();
                    if (str.length() > 0) {
                        map.put(lastKey, str);
                    }
                }
                sb.setLength(0);

                lastKey = line.substring(3).trim();
                if(lastKey.endsWith(":")) {
                    lastKey = lastKey.substring(0, lastKey.length() - 1);
                }
            } else {
                sb.append(line).append("\n");
            }
        }

        if(lastKey != null) {
            String str = sb.toString().trim();
            if (str.length() > 0) {
                map.put(lastKey, str);
            }
        }

    }

    public String get(Object key) {
        return map.get(key);
    }

    public Set<String> keySet() {
        return map.keySet();
    }

    public Set<Entry<String, String>> entrySet() {
        return map.entrySet();
    }

    public String getOrDefault(Object key, String defaultValue) {
        return map.getOrDefault(key, defaultValue);
    }

    public List<String> getLines(String key) {
        String str = get(key);
        if (str == null) {
            return Collections.emptyList();
        }
        return Arrays.asList(str.split("\n"));
    }

    public boolean containsKey(String key) {
        return map.containsKey(key);
    }
}
