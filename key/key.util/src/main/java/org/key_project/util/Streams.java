/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package org.key_project.util;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;

public class Streams {

    private Streams() {
        throw new Error("do not instantiate");
    }

    public static String toString(InputStream is) throws IOException {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        byte[] buf = new byte[2048];
        int count;
        while ((count = is.read(buf)) >= 0) {
            baos.write(buf, 0, count);
        }
        return new String(baos.toByteArray());
    }

}
