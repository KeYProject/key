pipeline {
  agent any
  stages {
    stage('Compile') {
      steps {
        sh '''cd key
pwd
ls -l'''
        sh 'cd key; ./gradlew classes'
      }
    }
  }
}