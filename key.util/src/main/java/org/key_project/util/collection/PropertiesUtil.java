/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.Properties;

public class PropertiesUtil {

    private PropertiesUtil() {
        throw new Error("do not instantiate");
    }

    public static void readLineBased(Properties properties, InputStream is) throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(is, StandardCharsets.UTF_8));
        String line;
        String currentKey = null;
        StringBuilder sb = new StringBuilder();

        while ((line = br.readLine()) != null) {
            if (line.startsWith("#")) {
            } else if (line.startsWith(" ") || line.startsWith("\t")) {
                if (sb.length() > 0) {
                    sb.append("\n");
                }
                sb.append(line.trim());
            } else {
                if (sb.length() > 0) {
                    if (currentKey == null) {
                        throw new IOException("No key defined");
                    }
                    properties.put(currentKey, sb.toString());
                    sb.setLength(0);
                }
            }
        }
        if (sb.length() > 0) {
            if (currentKey == null) {
                throw new IOException("No key defined");
            }
            properties.put(currentKey, sb.toString());
            sb.setLength(0);
        }

    }
}
