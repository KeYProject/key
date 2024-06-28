# JML Annotation Synthesis via Large Language Models

## Installation
To run the tool you need to initialize the jmlparser submodule.
```bash
git submodule init
git submodule update
```
Then we need to build the jmlparser submodule.
```bash
cd jmlparser
./mvnw clean install -Dmaven.test.skip=true
```
Afterwards you should have a jar file `jmlparser/javaparser-core/target/jmlparser-core-3.25.10-b6-SNAPSHOT.jar` which is required to run the tool.