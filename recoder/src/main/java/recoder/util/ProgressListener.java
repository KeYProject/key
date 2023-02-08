/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.util;

/**
 * A progress listener listens to process events issued by algorithms.
 *
 * @author AL
 * @since 0.72
 */
public interface ProgressListener {
    void workProgressed(ProgressEvent pe);
}
