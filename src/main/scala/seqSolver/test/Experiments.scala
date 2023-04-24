package seqSolver.test

object Experiments extends App{

  def time[R](block: => R)(name : String): R = {
    val t0 = System.currentTimeMillis()
    val result = block    // call-by-name
    val t1 = System.currentTimeMillis()
    println("----------------------")
    println(s"Running $name Test")
    println("Elapsed time: " + (t1 - t0) + "ms")
    println("----------------------")
    result
  }

  time {assert(QuickSort.run(false))}("Quicksort")

  time{assert(BakeryTest.runInv0(false))
  assert(BakeryTest.runInv1(false))
  assert(BakeryTest.runInv2(false))
  assert(BakeryTest.runInv3(false))}("Bakery Protocol")
  time{assert(DijkstraTest.run(false))}("Dijkstra")

  val sraTest = new SRATest


  time{assert(sraTest.test_PR_C2_Emptiness(false))}("PR C2 Emptiness")
  time{assert(sraTest.test_PR_C3_Emptiness(false))}("PR C3 Emptiness")
  time{assert(sraTest.test_PR_C4_Emptiness(false))}("PR C4 Emptiness")
  time{assert(sraTest.test_PR_C6_Emptiness(false))}("PR C6 Emptiness")
  time{assert(sraTest.test_PR_C9_Emptiness(false))}("PR C9 Emptiness")

  time{assert(sraTest.test_PR_CL2_Emptiness(false))}("PR CL2 Emptiness")
  time{assert(sraTest.test_PR_CL3_Emptiness(false))}("PR CL3 Emptiness")
  time{assert(sraTest.test_PR_CL4_Emptiness(false))}("PR CL4 Emptiness")
  time{assert(sraTest.test_PR_CL6_Emptiness(false))}("PR CL6 Emptiness")
  time{assert(sraTest.test_PR_CL9_Emptiness(false))}("PR CL9 Emptiness")

  time{assert(sraTest.test_IP_2_Emptiness(false))}("IP 2 Emptiness")
  time{assert(sraTest.test_IP_3_Emptiness(false))}("IP 3 Emptiness")
  time{assert(sraTest.test_IP_4_Emptiness(false))}("IP 4 Emptiness")
  time{assert(sraTest.test_IP_6_Emptiness(false))}("IP 6 Emptiness")
  time{assert(sraTest.test_IP_9_Emptiness(false))}("IP 9 Emptiness")


  time{assert(sraTest.test_PR_C2_Equiv(false))}("PR C2 Self Equivalence")
  time{assert(sraTest.test_PR_C3_Equiv(false))}("PR C3 Self Equivalence")
  time{assert(sraTest.test_PR_C4_Equiv(false))}("PR C4 Self Equivalence")
  time{assert(sraTest.test_PR_C6_Equiv(false))}("PR C6 Self Equivalence")
  time{assert(sraTest.test_PR_C9_Equiv(false))}("PR C9 Self Equivalence")

  time{assert(sraTest.test_PR_CL2_Equiv(false))}("PR CL2 Self Equivalence")
  time{assert(sraTest.test_PR_CL3_Equiv(false))}("PR CL3 Self Equivalence")
  time{assert(sraTest.test_PR_CL4_Equiv(false))}("PR CL4 Self Equivalence")
  time{assert(sraTest.test_PR_CL6_Equiv(false))}("PR CL6 Self Equivalence")
  time{assert(sraTest.test_PR_CL9_Equiv(false))}("PR CL9 Self Equivalence")

  time{assert(sraTest.test_PR_Ip2_Equiv(false))}("IP 2 Self Equivalence")
  time{assert(sraTest.test_PR_Ip3_Equiv(false))}("IP 3 Self Equivalence")
  time{assert(sraTest.test_PR_Ip4_Equiv(false))}("IP 4 Self Equivalence")
  time{assert(sraTest.test_PR_Ip6_Equiv(false))}("IP 6 Self Equivalence")
  time{assert(sraTest.test_PR_Ip9_Equiv(false))}("IP 9 Self Equivalence")

  time{assert(sraTest.test_PR_CL2_C2_Inclusion(false))}("CL 2 subset C2")
  time{assert(sraTest.test_PR_CL3_C3_Inclusion(false))}("CL 3 subset C3")
  time{assert(sraTest.test_PR_CL4_C4_Inclusion(false))}("CL 4 subset C4")
  time{assert(sraTest.test_PR_CL6_C6_Inclusion(false))}("CL 6 subset C6")
  time{assert(sraTest.test_PR_CL9_C9_Inclusion(false))}("CL 9 subset C9")

  time{assert(sraTest.test_PR_C2_CL2_Inclusion(false))}("C2 subset CL2")
  time{assert(sraTest.test_PR_C3_CL3_Inclusion(false))}("C3 subset CL3")
  time{assert(sraTest.test_PR_C4_CL4_Inclusion(false))}("C4 subset CL4")
  time{assert(sraTest.test_PR_C6_CL6_Inclusion(false))}("C6 subset CL6")
  time{assert(sraTest.test_PR_C9_CL9_Inclusion(false))}("C9 subset CL9")


  time{assert(sraTest.test_PR_IP3_IP2_Inclusion(false))}("Ip 3 subset Ip 2")
  time{assert(sraTest.test_PR_IP4_IP3_Inclusion(false))}("Ip 4 subset Ip 3")
  time{assert(sraTest.test_PR_IP6_IP4_Inclusion(false))}("Ip 6 subset Ip 4")
  time{assert(sraTest.test_PR_IP9_IP6_Inclusion(false))}("Ip 9 subset Ip 6")





}
