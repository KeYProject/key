pipeline {
  agent {
    docker {
      image 'wadoon/key-test-docker:jdk11'
    }
  }

  environment {
      GRADLE_OPTS = '-Dorg.gradle.daemon=false'
  }

  stages {
    stage('Clean') {
        sh 'javac -version'
        sh 'key/scripts/jenkins/startupClean.sh'
    }

    stage('Compile') {
        sh 'key/scripts/jenkins/deployAll.sh'
    }

    stage('Tests') {
      steps {
        sh 'key/scripts/jenkins/runTests.sh'
        junit(testResults: '*/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
      }    
    }
    
    stage('Docs') {
        sh 'key/scripts/jenkins/generateDoc.sh'
    }
  }
}
