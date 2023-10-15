package org.keyproject.key.api.data;

import java.io.File;
import java.util.List;

/**
 *
 * @param keyFile
 * @param javaFile
 * @param classPath
 * @param bootClassPath
 * @param includes
 */
public record LoadParams(File keyFile, File javaFile, List<File> classPath, File bootClassPath, List<File> includes) {}
