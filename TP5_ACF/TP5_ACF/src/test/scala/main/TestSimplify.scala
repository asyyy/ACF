package main

import library._
import org.junit.Assert._
import org.junit.Test
import simplifier.GUERIN._

class TestSimplify {
  @Test
  def t0(){
    val simp= new MySimplifier
    val p= List(Plus)
    val pres= List(Plus)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t1(){
    val simp= new MySimplifier
    val p= List(Qmark)
    val pres= List(Qmark)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t2(){
    val simp= new MySimplifier
    val p= List(Star)
    val pres= List(Star)
    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def t3(){
    val simp= new MySimplifier
    val p= List(Qmark,Qmark)
    val pres= List(Qmark,Qmark)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t4(){
    val simp= new MySimplifier
    val p= List(Qmark,Star)
    val pres= List(Plus)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t5(){
    val simp= new MySimplifier
    val p= List(Qmark,Plus)
    val pres= List(Qmark,Plus)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t6(){
    val simp= new MySimplifier
    val p= List(Star,Qmark)
    val pres= List(Plus)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t7(){
    val simp= new MySimplifier
    val p= List(Star,Star)
    val pres= List(Star)
    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def t8(){
    val simp= new MySimplifier
    val p= List(Star,Plus)
    val pres= List(Plus)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t9(){
    val simp= new MySimplifier
    val p= List(Plus,Qmark)
    val pres= List(Plus,Qmark)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t10(){
    val simp= new MySimplifier
    val p= List(Plus,Star)
    val pres= List(Plus)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t11(){
    val simp= new MySimplifier
    val p= List(Plus,Plus)
    val pres= List(Plus,Plus)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t12(){
    val simp= new MySimplifier
    val p= List(Char('a'))
    val pres= List(Char('a'))
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t13(){
    val simp= new MySimplifier
    val p= List(Char('a'),Char('b'))
    val pres= List(Char('a'),Char('b'))
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t14(){
    val simp= new MySimplifier
    val p= List(Char('a'),Star)
    val pres= List(Char('a'),Star)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t15(){
    val simp= new MySimplifier
    val p= List(Char('a'),Qmark)
    val pres= List(Char('a'),Qmark)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t16(){
    val simp= new MySimplifier
    val p= List(Char('a'),Plus)
    val pres= List(Char('a'),Plus)
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t17(){
    val simp= new MySimplifier
    val p= List()
    val pres= List()
    assertEquals(pres, simp.simplify(p))
  }
  @Test
  def t18(){
    val simp= new MySimplifier
    val p1 : String = "aaa???++"
    val p2 = Parser.parseSymbolList(p1)
    val pres1 : String = "aaa???++"
    val pres2 = Parser.parseSymbolList(pres1)
    assertEquals(pres2, simp.simplify(p2))
  }
  @Test
  def t19(){
    val simp= new MySimplifier
    val p : String = "a**?**"
    val p2 = Parser.parseSymbolList(p)
    val pres : String = "a*+*"
    val pres2 = Parser.parseSymbolList(pres)
    assertEquals(pres2, simp.simplify(p2))
  }
  @Test
  def t20(){
    val simp= new MySimplifier
    val p : String = "a**?**b"
    val p2 = Parser.parseSymbolList(p)
    val pres : String = "a*+*b"
    val pres2 = Parser.parseSymbolList(pres)
    assertEquals(pres2, simp.simplify(p2))
  }
  @Test
  def t21(){
    val simp= new MySimplifier
    val p : String = "++++b*"
    val p2 = Parser.parseSymbolList(p)
    val pres : String = "++++b*"
    val pres2 = Parser.parseSymbolList(pres)
    assertEquals(pres2, simp.simplify(p2))
  }
  @Test
  def t22(){
    val simp= new MySimplifier
    val p : String = "+*b*+"
    val p2 = Parser.parseSymbolList(p)
    val pres : String = "+b+"
    val pres2 = Parser.parseSymbolList(pres)
    assertEquals(pres2, simp.simplify(p2))
  }
  @Test
  def t23(){
    val simp= new MySimplifier
    val p : String = "+*b*+"
    val p2 = Parser.parseSymbolList(p)
    val pres : String = "+b+"
    val pres2 = Parser.parseSymbolList(pres)
    assertEquals(pres2, simp.simplify(p2))
  }






}