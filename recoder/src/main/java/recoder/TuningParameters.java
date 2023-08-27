/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

/**
 * @author Tobias
 */
public interface TuningParameters {
    int INITIAL_CROSS_REFERENCER_ELEMENT2REFERENCE_HASH_SET_SIZE = 4;
    int INITIAL_SOURCE_INFO_NAME2PRIMITIVE_HASH_SET_SIZE = 64;
    int INITIAL_SOURCE_INFO_REFERENCE2ELEMENT_HASH_SET_SIZE = 1024;
}
