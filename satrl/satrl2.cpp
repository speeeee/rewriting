#include <cstdio>
#include <cstdlib>

#include <vector>
#include <tuple>
#include <regex>
#include <string>
#include <unordered_map>
#include <istream>
#include <fstream>
#include <sstream>

#define SELF  0
#define STORE 1

#define ATOM 0
#define RVAR 1
#define VAR  2

#define BUFMAX 256

struct Item { std::string dat; int type;
              Item(std::string _d, int _t) {
                dat = _d; type = _t; }
              Item() { type = ATOM; } };
/*void item_print(Item a) {
  if(a->type == GRP) { printf("(");
    for(int i=0;i<a->grp.size();i++) { item_print(a->grp[i]); }
    printf (")"); } else { printf(" %s ",a->dat.c_str()); } }*/
std::string show_stk(std::vector<Item> a) { std::stringstream s;
  for(int i=0;i<a.size()-1;i++) { if(a[i].dat=="("||a[i+1].dat==")") { s << a[i].dat; }
    else { s << a[i].dat << " "; } }
  s << a[a.size()-1].dat;
  return s.str(); }
bool operator==(Item a, Item b) { if(a.type!=b.type&&a.type!=VAR &&b.type!=VAR
                                                   &&a.type!=RVAR&&b.type!=RVAR) { return false; }
  switch(b.type) { case ATOM: return a.dat==b.dat; break;
                   case RVAR: { std::stringstream s(b.dat); std::string reg; s >> reg;
                                return std::regex_match(a.dat,std::regex(reg)); break; }
                   case VAR: return true; } }
// typedef std::vector<Item> Stk;
struct Term { std::string var; std::vector<Item> r;
              Term(std::string _v, std::vector<Item> _r) { var = _v; r = _r; }
              Term() { } };
struct Rule { int loc; int outtype; std::vector<Item> in; std::vector<Item> out;
              std::unordered_map<std::string,std::vector<Item>> ts; int exprn;
              Rule(int _o, std::vector<Item> _in, std::vector<Item> _out) {
                ts = std::unordered_map<std::string,std::vector<Item>>();
                in = _in, out = _out; outtype = _o; exprn = 0; loc = 0; } };
Item rules_loc(Rule r, int loc) { return r.in[loc]; }

std::vector<Rule> d_rules = { Rule(STORE
                                  ,(std::vector<Item>){ Item("Rule",ATOM), Item("$a",VAR), Item("$b",VAR) }
                                  ,std::vector<Item>())
                             /*,Rule(SELF
                                  ,(std::vector<Item>){ Item("Just",ATOM), Item("$a",VAR) }
                                  ,(std::vector<Item>){ Item("$a",VAR) })*/ };

std::vector<Item> w_close(std::vector<Item> a) { if(a[0].dat!="(") { return a; }
  a.pop_back(); std::vector<Item> ret(a.size()-1); for(int i=0;i<ret.size();i++) { ret[i] = a[i+1]; }
  return ret; }

// warning: modifies rules
std::vector<Item> exec_rule(std::vector<Item> expr, std::vector<Rule> &rules, Rule a) {
  /*p_stk(expr); p_stk(a.in); return a.out;*/
  std::vector<Item> ret;
  if(a.outtype==STORE) { auto qa = a.ts["$a"]; auto qb = a.ts["$b"];
    rules.push_back(Rule(SELF,w_close(qa),w_close(qb))); }
  else {
    for(int i=0;i<a.out.size();i++) {
      if(a.out[i].type==VAR) { auto q = a.ts[a.out[i].dat];
                               ret.insert(ret.end(),q.begin(),q.end()); }
      else { ret.push_back(a.out[i]); } } }
  int q = 0; int exprn = 0;
  for(int i=0;i<a.in.size();q++) { if(expr[expr.size()-1-q].dat=="(") { exprn--; }
    else if(expr[expr.size()-1-q].dat==")") { exprn++; }
    if(!exprn) { i++; } }
  expr.resize(expr.size()-q); expr.insert(expr.end(),ret.begin(),ret.end()); return expr; }

// modifies locs
// warning: not well written
std::vector<Item> match_rule(std::vector<Item> expr, Item q, std::vector<Rule> &rules, std::vector<int> &locs) {
  for(int i=0;i<rules.size();i++) { Item e = rules_loc(rules[i],locs[i]);
    if(q==e) {
      if(e.type==VAR) { if(q.dat=="(") { rules[i].exprn++; }
        else if(q.dat==")") { rules[i].exprn--; }
        //else if(rules[i].exprn) { rules[i].ts[rules_loc(rules[i],locs[i]).dat].push_back(q); }
        rules[i].ts[e.dat].push_back(q);
        if(!rules[i].exprn) { locs[i]++; } }
      else if(e.type==RVAR) { std::stringstream s(e.dat); std::string reg; std::string var;
        s >> reg >> var;
        rules[i].ts[var].push_back(q); locs[i]++; }
      else { locs[i]++; } }
    else { locs[i] = 0; }
    if(locs[i]>=rules[i].in.size()) {
      locs[i] = 0; expr.push_back(q);
      expr = exec_rule(expr,rules,rules[i]);
      rules[i] = Rule(rules[i].outtype,rules[i].in,rules[i].out); return expr; } }
  expr.push_back(q); return expr; }

template <typename T>
std::vector<Item> lex_and_parse(T &a, std::vector<Rule> rules, std::vector<Item> vars) {
  auto locs = std::vector<int>(rules.size(),0);
  for(int i=0;i<locs.size();i++) { locs[i] = rules[i].loc; }
  a >> std::ws; std::vector<Item> expr;
  while(!a.eof()) { a >> std::ws; switch(a.peek()) {
    case EOF: break;
    case ')': { a.ignore(1); expr = match_rule(expr,Item(")",ATOM),rules,locs);
                break; }
    case '(': { a.ignore(1); expr = match_rule(expr,Item("(",ATOM),rules,locs);
                break; }
    case '$': { std::string q; a >> q; while(q.back()==')') { q.pop_back(); a.putback(')'); }
                expr = match_rule(expr,Item(q,VAR),rules,locs); break; }
    case '\\': { a.ignore(1); std::string qr; std::getline(a,qr,'\\');
                 std::string q; a >> q; while(q.back()==')') { q.pop_back(); a.putback(')'); }
                 qr += " " + q;
                 expr = match_rule(expr,Item(qr,RVAR),rules,locs); break; }
    default: { std::string q; a >> q; while(q.back()==')') { q.pop_back(); a.putback(')'); }
               expr = match_rule(expr,Item(q,ATOM),rules,locs); break; } } }
  d_rules = rules; return expr; }

// DONE: add simple file imports and regex-match support.
int main(int argc, char **argv) {
  std::ifstream file; file.open(argv[1]);
  // DONE: create 'show' function for Stks and continue parsing until in normal form.
  std::vector<Item> f; std::string f_show = show_stk(lex_and_parse(file,d_rules,std::vector<Item>()));
  while(true) { std::stringstream f_s(f_show);
    printf("%s\n",f_show.c_str());
    f = lex_and_parse(f_s,d_rules,std::vector<Item>());
    if(show_stk(f)==f_show) { break; } else { f_show = show_stk(f); } }
  printf("%s\n",show_stk(f).c_str());
  /*item_destroy(f);*/ return 0; }
