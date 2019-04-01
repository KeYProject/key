pipeline {
  agent any
  stages {
    stage('Compile') {
      steps {
        sh '''cd key; ./gradlew classes'''
      }
    }
  }
}
