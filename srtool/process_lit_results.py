import glob
import sys
import os

def wrongFormat():
    print "Test results were not in expected format.  Talk to Ally to debug this."
    sys.exit(1)

def sanityCheckResult(result, testNames):
    filename = result.split(" ")[3]
    if not filename in testNames:
        wrongFormat()
    testNames.remove(filename)

def resultExactlyMatches(result, expected):
    assert result.split(' ')[0] == "FAIL:"
    path = result.split(' ')[3]
    tempfileName = os.path.join(os.path.split(path)[0], "Output", os.path.split(path)[1] + ".tmp")
    if not os.path.isfile(tempfileName):
        return False

    with open(tempfileName) as tempfile:
        lines = tempfile.readlines()
        if len(lines) != 1:
            return False
        return lines[0].strip() == expected

def resultIsUnknown(result):
  return resultExactlyMatches(result, "UNKNOWN")

def resultIsWrong(result):
  path = result.split(' ')[3]
  natureOfResult = path.split('/')[2]
  if natureOfResult == "correct":
      return resultExactlyMatches(result, "INCORRECT")
  assert natureOfResult == "incorrect"
  return resultExactlyMatches(result, "CORRECT")

def checkTestResults():

    part1TestNames = glob.glob("__acceptancetests/part1/*/*.c")
    part2TestNames = glob.glob("__acceptancetests/part2/*/*.c")

    part1NumTests = len(part1TestNames)
    part2NumTests = len(part2TestNames)

    part1ResultsFileName = sys.argv[1]
    part2ResultsFileName = sys.argv[2]
    jsonFileName = sys.argv[3]

    part1NumPasses = 0
    part1NumFails = 0

    with open(part1ResultsFileName) as part1ResultsFile:
      part1ResultsData = part1ResultsFile.readlines()
      i = 0
      for resultsLine in part1ResultsData:
        if i == 0:
            pass
        else:
            if resultsLine.startswith("PASS: SRT :: "):
                sanityCheckResult(resultsLine, part1TestNames)
                part1NumPasses += 1
            elif resultsLine.startswith("FAIL: SRT :: "):
                sanityCheckResult(resultsLine, part1TestNames)
                part1NumFails += 1
        i += 1

    part2NumPasses = 0
    part2NumUnknowns = 0
    part2NumWrongResults = 0
    part2NumGobbledygooks = 0

    with open(part2ResultsFileName) as part2ResultsFile:
      part2ResultsData = part2ResultsFile.readlines()
      i = 0
      for resultsLine in part2ResultsData:
        if i == 0:
            pass
        else:
            if resultsLine.startswith("PASS: SRT :: "):
                sanityCheckResult(resultsLine, part2TestNames)
                part2NumPasses += 1
            elif resultsLine.startswith("FAIL: SRT :: "):
                sanityCheckResult(resultsLine, part2TestNames)
                if resultIsUnknown(resultsLine):
                    part2NumUnknowns += 1
                elif resultIsWrong(resultsLine):
                    part2NumWrongResults += 1
                else:
                    part2NumGobbledygooks += 1
        i += 1

    part1Score = part1NumPasses - 2*part1NumFails
    print "Part 1 tests (for information only)"
    print "==================================="
    print "#passes: " + str(part1NumPasses)
    print "#fails:  " + str(part1NumFails)
    print "score:   " + str(part1Score) + "/" + str(part1NumTests)
    print ""

    part2Score = 2*part2NumPasses + (-1)*part2NumGobbledygooks + (-4)*part2NumWrongResults
    print "Part 2 tests"
    print "============"
    print "#passes:        " + str(part2NumPasses) + " (cases where your tool accurately classified a program)"
    print "#wrong results: " + str(part2NumWrongResults) + " (cases where your tool got the classification wrong)"
    print "#unknowns:      " + str(part2NumUnknowns) + " (cases where your tool gracefully reported UNKNOWN)"
    print "#gobbledygooks: " + str(part2NumGobbledygooks) + " (cases where your tool output something other than simply 'CORRECT', 'INCORRECT' or 'UNKNOWN')"
    print "#not executed:  " + str(part2NumTests - (part2NumPasses + part2NumWrongResults + part2NumUnknowns + part2NumGobbledygooks)) + " (tests that were not reached due to your tool being too slow)"
    print "score:          " + str(part2Score) + "/" + str(2*part2NumTests)

    with open(jsonFileName, 'w') as jsonFile:
      jsonFile.write("[ { \"score\":" + str(part2Score) + ", \"name\": \"Tests\", \"possible\": " + str(2*part2NumTests) + "} ]\n")



if __name__ == '__main__':
    checkTestResults()

