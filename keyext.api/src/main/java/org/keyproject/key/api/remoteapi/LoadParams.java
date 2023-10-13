package org.keyproject.key.api.remoteapi;

import java.io.File;
import java.util.List;

public record LoadParams(File keyFile, File javaFile, List<File> classPath, File bootClassPath, List<File> includes) {

}
