
#include <algorithm>
#include <any>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <ctime>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <list>
#include <map>
#include <queue>
#include <random>
#include <set>
#include <signal.h>
#include <sstream>
#include <stack>
#include <stdexcept>
#include <stdio.h>
#include <string>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include <unordered_map>
#include <utility>
#include <vector>
class node {
  public:
  size_t node_id;
  int max_cap;
  int cap;
  int type;
  int pw_actual, pw_excess, pw_buy;
  int L_FE, L_buy;
  int grid_id;
  node() = default;
  node(int max_cap, size_t cap, int type)
      : max_cap(max_cap), cap(cap), type(type) {}
  node(int max_cap, size_t cap, int type, size_t node_id)
      : node_id(node_id), max_cap(max_cap), cap(cap), type(type) {
    init_pw();
  }
  bool is_grid() { return type != 0; }
  bool charge(int amount) {
    if (!is_grid())
      return false;
    if (amount < 0)
      return false;
    cap = std::min(max_cap, cap + amount);
    return true;
  }
  bool consume(int amount) {
    if (!is_grid())
      return false;
    if (amount < 0)
      return false;
    if (amount > cap)
      return false;
    cap -= amount;
    return true;
  }
  void init_pw() {
    pw_actual = 0;
    pw_excess = 0;
    pw_buy = 0;
    L_FE = 0;
    L_buy = 0;
  }
  void print(FILE *fp) {
    fprintf(fp, "%zu %d %d %d %d\n", node_id + 1, cap, pw_actual, pw_excess,
            pw_buy);
  }
};
class vertex {
  public:
  int x, y, p, A, l;
};
class edge {
  public:
  using cost_type = int_fast64_t;
  static const cost_type INF = 1LL << 28;
  size_t src, dst;
  cost_type cost;
  int bit;
  edge() : cost(INF) {}
  edge(size_t u, size_t v, cost_type c) : src(u), dst(v), cost(c), bit(0) {}
  edge(size_t u, size_t v, cost_type c, int b)
      : src(u), dst(v), cost(c), bit(b) {}
};
const edge::cost_type INF = 1LL << 28;
template <typename edge_type> class graph {
  public:
  using cost_type = typename edge_type::cost_type;
  std::vector<std::vector<edge_type>> g;
  std::vector<node> nodes;
  graph() = default;
  graph(size_t N) : g(N), nodes(N) {
    for (size_t i = 0; i < N; i++) {
      nodes[i].type = 0;
    }
  }
  graph(const graph &g_) : g(g_.g), nodes(g_.nodes) { sort_edges(); }
  graph<edge_type> &operator=(const graph<edge_type> &g_) {
    g = g_.g;
    nodes = g_.nodes;
    sort_edges();
    return *this;
  }
  size_t size() const { return g.size(); }
  const std::vector<edge_type> &operator[](int k) const { return g[k]; }
  std::vector<edge_type> &operator[](int k) { return g[k]; }
  void add_edge(size_t u, size_t v, cost_type c) { g[u].emplace_back(u, v, c); }
  void add_edge(size_t u, size_t v, cost_type c, int b) {
    g[u].emplace_back(u, v, c, b);
  }
  void set_node(size_t u, node n) { nodes[u] = n; }
  void sort_edges() {
    for (size_t i = 0; i < g.size(); i++) {
      std::sort(g[i].begin(), g[i].end(),
                [](edge_type a, edge_type b) { return a.dst < b.dst; });
    }
  }
  int find(size_t u, size_t v) {
    for (size_t i = 0; i < g[u].size(); i++) {
      if (g[u][i].dst == v)
        return i;
    }
    return -1;
  }
  void print_all_nodes(FILE *fp) {
    for (auto i : nodes) {
      if (i.is_grid())
        i.print(fp);
    }
  }
  void load_raw_data(double resolution, FILE *fp) {
    size_t V, E;
    fscanf(fp, "%zu %zu\n", &V, &E);
    nodes.resize(V);
    for (size_t i = 0; i < V; i++) {
      nodes[i].type = 0;
    }
    g.clear();
    g.resize(V);
    size_t u, v;
    int c;
    for (size_t i = 0; i < E; ++i) {
      fscanf(fp, "%zu %zu %d\n", &u, &v, &c);
      c = std::ceil(c / resolution);
      if (--u < --v)
        g[u].emplace_back(u, v, c);
      else
        g[v].emplace_back(v, u, c);
    }
  }
};
class position {
public:
 size_t from;
 size_t to;
 size_t distance;
 size_t edge_distance;
 position() = default;
 position(size_t from, size_t to, size_t distance, size_t edge_distance) :
  from(from), to(to), distance(distance), edge_distance(edge_distance) {}
 bool on_vertex() {
  if (distance == 0 || distance == edge_distance) {
   return true;
  }
else {
   return false;
  }
 }
 int now_vertex() {
  if (on_vertex()) {
   if (distance == 0) {
    return from;
   }
   else {
    return to;
   }
  }
  return -1;
 }
 size_t rest_distance() {
  return edge_distance - distance;
 }
};
class vehicle {
  public:
  int max_cap;
  int cap;
  position pos;
  std::set<size_t> orders;
  size_t delta_move;
  int V_in_Max_EV;
  int V_out_Max_EV;
  int N_Max_Trans;
  vehicle() = default;
  vehicle(int max_cap, int cap, position pos)
      : max_cap(max_cap), cap(cap), pos(pos) {}
  bool charge(int amount) {
    if (amount < 0)
      return false;
    cap = std::min(max_cap, cap + amount);
    return true;
  }
  bool consume(int amount) {
    if (amount < 0)
      return false;
    if (amount > cap)
      return false;
    cap -= amount;
    return true;
  }
  bool set_position(position p) {
    pos = p;
    return true;
  }
  int now_vertex() { return pos.now_vertex(); }
  void add_order(size_t id) {
    orders.insert(id);
  }
  void erase_order(size_t id) { orders.erase(id); }
};
class order {
  public:
  size_t order_id;
  int start_time;
  int end_time;
  int from;
  int to;
  int vehicle_id;
  order() = default;
  order(size_t order_id, int start_time, int from, int to)
      : order_id(order_id), start_time(start_time), end_time(-1), from(from),
        to(to), vehicle_id(-1) {}
  void print(FILE *fp) {
    fprintf(fp, "%zu %d %d %d %d\n", order_id + 1, from + 1, to + 1,
            vehicle_id == -1 ? 0 : 1,
            start_time);
  }
};
class in_order {
  public:
  std::vector<int> in_order_1_ndiv;
};
class OrderB {
  public:
  int id;
  int status;
  int orig;
  int dest;
  int startTime;
  int endTime;
  int vehicle_id;
  bool sendFlag;
  OrderB(int orig, int dest, int startTime)
      : id(-1), orig(orig), dest(dest), startTime(startTime),
        status(0), vehicle_id(-1), endTime(-1), sendFlag(false) {}
};
class energy {
  public:
  size_t id;
  int actual;
  energy() = default;
  energy(size_t id, int actual) : id(id), actual(actual) {}
};
       
std::string to_string(const std::string &str) { return str; }
template <class T>
std::string to_string(const std::vector<T> &vec, char delim = ' ') {
  using namespace std;
  string ret = "";
  for (size_t i = 0; i < vec.size(); ++i) {
    if (i > 0)
      ret += delim;
    ret += to_string(vec[i]);
  }
  return ret;
}
template <class T, class U> std::string to_string(const std::pair<T, U> &p) {
  using namespace std;
  return "(" + to_string(p.first) + ", " + to_string(p.second) + ")";
}
       
enum RadiationCalcType {
  CT_PREDICT,
  CT_ACTUAL,
  CT_DUMMY,
};
class weather_info {
  public:
  std::vector<std::vector<double>> R;
  weather_info() : weather_info(0, 0) {}
  weather_info(size_t n_weather, size_t n_div)
      : R(n_weather, std::vector<double>(n_div, 0)) {}
};
std::ostream &operator<<(std::ostream &dest, const weather_info &rad) {
  for (auto &R : rad.R) {
    for (auto &r : R)
      dest << r << " ";
    dest << "\n";
  }
  return dest;
}
class radiation {
  public:
  const size_t N_dummy = 10;
  size_t N_day;
  size_t N_weather;
  size_t N_div;
  std::vector<int> station_x;
  std::vector<weather_info> weather_info_predict;
  std::vector<weather_info> weather_info_actual;
  std::vector<std::vector<weather_info>> weather_info_dummy;
  radiation() { init(0, 0, 0); }
  radiation(size_t n_day, size_t n_weather, size_t n_div) {
    init(n_day, n_weather, n_div);
  }
  void init(size_t n_day, size_t n_weather, size_t n_div) {
    N_day = n_day;
    N_weather = n_weather;
    N_div = n_div;
    station_x.resize(n_weather);
    weather_info_predict =
    std::vector<weather_info>(N_day, weather_info(N_weather, N_div));
    weather_info_actual =
    std::vector<weather_info>(N_day, weather_info(N_weather, N_div));
    weather_info_dummy = std::vector<std::vector<weather_info>>(
    N_dummy, std::vector<weather_info>(N_day, weather_info(N_weather, N_div)));
  }
};
class shelter_info {
public:
    int x;
    int p;
    shelter_info(int X, int P): x(X), p(P){}
    shelter_info(): x(0), p(0){}
};
class shelter {
public:
    size_t N_shelter;
    std::vector<shelter_info> shelter_data;
    std::vector<int> shelter_D;
    shelter(size_t n_shelter = 0, size_t n_div = 0) {
        init(n_shelter, n_div);
    }
    void init(size_t n_shelter, size_t n_div) {
        N_shelter = n_shelter;
        shelter_data.resize(n_shelter);
        shelter_D.resize(n_div);
    }
};
       
class TimeHelper {
  public:
  static long long currentTimeMillis() {
    auto epoch = std::chrono::high_resolution_clock::from_time_t(0);
    auto now = std::chrono::high_resolution_clock::now();
    long long mseconds =
    std::chrono::duration_cast<std::chrono::milliseconds>(now - epoch).count();
    return mseconds;
  }
};
class RandomHelper {
  unsigned int Seed;
  public:
  RandomHelper(unsigned int seed = 0) {
    Seed = seed;
    if (Seed == 0) {
      Seed = time(NULL);
    }
    srand(Seed);
  }
  void reset_seed() { srand(Seed); }
  void set_seed(unsigned int seed) { srand(seed); }
  int nextInt() { return rand(); }
  int nextInt(int bound) { return (rand() % bound); }
  int nextInt(int lbound, int ubound) {
    return (rand() % (ubound - lbound) + lbound);
  }
};
extern RandomHelper random_helper;
class VectorHelper {
  public:
  template <class T> static void fill(std::vector<T> &vec, T val) {
    for (typename std::vector<T>::iterator it = vec.begin(); it != vec.end();
         ++it) {
      *it = val;
    }
  }
  template <class T> static void fillPtr(std::vector<T *> &vec, T *val) {
    for (typename std::vector<T *>::iterator it = vec.begin(); it != vec.end();
         ++it) {
      *it = val;
    }
  }
};
class StringHelper {
  public:
  static int SplitToken(const std::string &sStr,
                        const std::string &sTokenSet,
                        std::vector<std::string> &sResult) {
    sResult.clear();
    const int &slen = sStr.length();
    if (slen == 0)
      return sResult.size();
    int toknum = sTokenSet.length();
    if (toknum > 0) {
      char *pStr = new char[slen + 1];
      if (pStr) {
        memcpy(pStr, sStr.c_str(), slen + 1);
        const char *pTok = sTokenSet.c_str();
        char *pch = strtok(pStr, pTok);
        while (pch != NULL) {
          sResult.push_back(pch);
          pch = strtok(NULL, pTok);
        }
        delete[] pStr;
        pStr = nullptr;
      }
    }
    return sResult.size();
  }
};
class score2 {
  public:
  double w_trans = 1.0;
  double w_ele = 1.0;
  double w_env = 1.0;
  double w_acc = 1.0;
  double w_work = 1.0;
  std::vector<int> w_days;
  int alpha_cost = 0.0;
  double alpha_trans_fee = 0.0;
  double alpha_trans_penalty = 0.0;
  double alpha_trans_canceled = 0.0;
  double alpha_trans_undelivered = 0.0;
  double alpha_ele = 0.0;
  double alpha_ele_FE = 0.0;
  double alpha_ele_buy = 0.0;
  double alpha_env = 0.0;
  double alpha_env_fuel = 0.0;
  double alpha_env_buy = 0.0;
  int alpha_acc = 0.0;
  int alpha_work = 0;
};
class Demand_Info {
  public:
  int x;
  int sigma_D2;
  std::vector<int> D_predict_list;
  Demand_Info(size_t N_div = 0) : x(-1), sigma_D2(-1), D_predict_list(N_div) {}
  void dump(FILE *fp) {
    fprintf(fp, "BEGIN DUMP of Demand_Info {\n");
    fprintf(fp, "  %d %d\n  ", x, sigma_D2);
    for (size_t i = 0; i < D_predict_list.size(); i++) {
      fprintf(fp, "%d ", D_predict_list[i]);
    }
    fprintf(fp, "}\n");
  }
};
class Demand {
  public:
  size_t N_day;
  size_t N_demand;
  size_t N_div;
  std::vector<std::vector<Demand_Info>> day_list;
  Demand() : Demand(0, 0, 0) {}
  Demand(size_t N_day, size_t N_demand, size_t N_div)
      : N_day(N_day), N_demand(N_demand), N_div(N_div),
        day_list(N_day,
                 std::vector<Demand_Info>(N_demand, Demand_Info(N_div))) {}
};
class PV_info {
  public:
  int A_PV;
  int C_PV_init;
};
class FE_info {
  public:
  int P_FE_min;
  int P_FE_max;
  int Eta_FE_min;
  int Eta_FE_max;
  int C_FE_init;
  int C_FE_fuel;
  int EL_FE;
};
class RB_info {
  public:
  int P_RB_charge;
  int P_RB_discharge;
  int Eta_RB;
  int Cap_RB;
  int C_RB_init;
};
class EVC_info {
  public:
  int P_EVC_in;
  int P_EVC_out;
  int C_EVC_init;
};
class V_info {
  public:
  int Cap_V_ele;
  int Cap_V_pop;
  int P_V_charge;
  int P_V_discharge;
  int C_V_init;
  int Delta_V_move;
};
class asset {
  public:
  size_t N_PV;
  size_t N_FE;
  size_t N_RB;
  size_t N_EVC;
  size_t N_V;
  std::vector<PV_info> PV_list;
  std::vector<FE_info> FE_list;
  std::vector<RB_info> RB_list;
  std::vector<EVC_info> EVC_list;
  std::vector<V_info> V_list;
  asset(size_t n_pv = 0,
        size_t n_fe = 0,
        size_t n_rb = 0,
        size_t n_evc = 0,
        size_t n_v = 0) {
    init(n_pv, n_fe, n_rb, n_evc, n_v);
  }
  void init(size_t n_pv, size_t n_fe, size_t n_rb, size_t n_evc, size_t n_v) {
    init_PV(n_pv);
    init_FE(n_fe);
    init_RB(n_rb);
    init_EVC(n_evc);
    init_V(n_v);
  }
  void init_PV(size_t n_pv) {
    N_PV = n_pv;
    PV_list.resize(n_pv);
  }
  void init_FE(size_t n_fe) {
    N_FE = n_fe;
    FE_list.resize(n_fe);
  }
  void init_RB(size_t n_rb) {
    N_RB = n_rb;
    RB_list.resize(n_rb);
  }
  void init_EVC(size_t n_evc) {
    N_EVC = n_evc;
    EVC_list.resize(n_evc);
  }
  void init_V(size_t n_v) {
    N_V = n_v;
    V_list.resize(n_v);
  }
  const PV_info *getPVinfo(size_t idx) {
    if (not(idx < N_PV)) {
      ;
      ;
      exit(1);
    }
    return &PV_list[idx];
  }
  const RB_info *getRBinfo(size_t idx) {
    if (not(idx < N_RB)) {
      ;
      ;
      exit(1);
    }
    return &RB_list[idx];
  }
  const EVC_info *getEVCinfo(size_t idx) {
    if (not(idx < N_EVC)) {
      ;
      ;
      return nullptr;
    }
    return &EVC_list[idx];
  }
  const FE_info *getFEinfo(size_t idx) {
    if (not(idx < N_FE)) {
      ;
      ;
      return nullptr;
    }
    return &FE_list[idx];
  }
};
class grid_info_data {
  public:
  int x_grid_pos = 0;
  int d_grid = 0;
  int chg_grid_init = 0;
  int type_grid_PV = 0;
  int A_grid_PV = 0;
  int type_grid_FE = 0;
  int type_grid_RB = 0;
  int A_grid_RB = 0;
  int type_grid_EVC = 0;
  bool hasDemandInfo = false;
  void dump(FILE *fp) {
    fprintf(fp, "BEGIN DUMP of grid_info_data {\n");
    fprintf(fp, "  %d %d\n", x_grid_pos, chg_grid_init);
    fprintf(fp, "  %d %d\n", type_grid_PV, A_grid_PV);
    fprintf(fp, "  %d\n", type_grid_FE);
    fprintf(fp, "  %d %d\n", type_grid_RB, A_grid_RB);
    fprintf(fp, "  %d\n", type_grid_EVC);
    fprintf(fp, "}\n");
  }
};
class grid_info {
  public:
  size_t N_grid;
  std::vector<grid_info_data> data_list;
  grid_info(size_t n_grid = 0) { init(n_grid); }
  void init(size_t n_grid) {
    N_grid = n_grid;
    data_list.resize(n_grid);
  }
};
class EV_info_data {
  public:
  int x_EV_pos = 0;
  int Chg_EV_init = 0;
  int type_EV = 0;
};
class EV_info {
  public:
  size_t N_EV;
  std::vector<EV_info_data> data_list;
  EV_info(size_t n_ev = 0) { init(n_ev); }
  void init(size_t n_ev) {
    N_EV = n_ev;
    data_list.resize(n_ev);
  }
  const EV_info_data *getEvInfoByType(int typeEV) {
    for (size_t i = 0; i < N_EV; i++) {
      if (data_list[i].type_EV == typeEV) {
        return &(data_list[i]);
      }
    }
    return nullptr;
  }
  void dump(FILE *fp) {
    for (auto const &v : data_list) {
      fprintf(fp, "%d %d %d\n", v.x_EV_pos, v.Chg_EV_init, v.type_EV);
    }
  }
};
       
       
class RectangularVectors {
public:
    static std::vector<std::vector<int>> RectangularIntVector(int size1, int size2) {
        std::vector<std::vector<int>> newVector(size1);
        for (int vector1 = 0; vector1 < size1; vector1++) {
            newVector[vector1] = std::vector<int>(size2);
        }
        return newVector;
    }
};
       
class StringBuilder {
private:
 std::string privateString;
public:
 StringBuilder() {
 }
 StringBuilder(const std::string &initialString) {
  privateString = initialString;
 }
 StringBuilder(std::size_t capacity) {
  ensureCapacity(capacity);
 }
 char charAt(std::size_t index) {
  return privateString[index];
 }
 StringBuilder *append(const std::string &toAppend) {
  privateString += toAppend;
  return this;
 }
 template<typename T>
 StringBuilder *append(const T &toAppend) {
  privateString += toString(toAppend);
  return this;
 }
 StringBuilder *insert(std::size_t position, const std::string &toInsert) {
  privateString.insert(position, toInsert);
  return this;
 }
 template<typename T>
 StringBuilder *insert(std::size_t position, const T &toInsert) {
  privateString.insert(position, toString(toInsert));
  return this;
 }
 std::string toString() {
  return privateString;
 }
 std::size_t length() {
  return privateString.length();
 }
 void setLength(std::size_t newLength) {
  privateString.resize(newLength);
 }
 std::size_t capacity() {
  return privateString.capacity();
 }
 void ensureCapacity(std::size_t minimumCapacity) {
  privateString.reserve(minimumCapacity);
 }
 StringBuilder *remove(std::size_t start, std::size_t end) {
  privateString.erase(start, end - start);
  return this;
 }
 StringBuilder *replace(std::size_t start, std::size_t end, const std::string &newString) {
  privateString.replace(start, end - start, newString);
  return this;
 }
private:
 template<typename T>
 static std::string toString(const T &subject) {
  std::ostringstream ss;
  ss << subject;
  return ss.str();
 }
};
int is_first = 0;
class Grid {
  public:
  int charge = 0, vertex = 0, turnCharge = 0, prevActual = 0, prevBuy = 0,
      prevExcess = 0, numVehicles = 0, evalCharge = 0,
      predictedEnergyBalanceType = 0;
  int grid_id = 0;
  int V_in_Max = 0;
  int V_out_Max = 0;
  int Cap_RB_total = 0;
  const RB_info *rb = nullptr;
  const FE_info *fe = nullptr;
  const EVC_info *evc = nullptr;
  int P_FE = 0;
  std::vector<int> predictedEnergyBalanceBase, predictedEnergyBalanceWithOrders;
  bool is_nano = false;
  int prevFE = 0;
  int prevLbuy = 0;
};
class Vehicle {
  public:
  int vertex0 = 0;
  int vertex1 = 0, vertex2 = 0, dist1 = 0, dist2 = 0, charge = 0, target = 0,
      evalCharge = 0, evalVertex = 0, C_e_init = 0, C_e_max = 0;
  std::string last_command;
  int V_in_max = 0;
  int V_out_max = 0;
  int N_max = 0;
  int Delta_move = 0;
  std::vector<int> adj;
  std::vector<int> carryingOrderIds;
  int id = 0;
  Vehicle(int vertex) : Vehicle(vertex, vertex, 0, 0) {}
  Vehicle(int v1, int v2, int d1, int d2)
      : vertex0(v1), vertex1(v1), vertex2(v2), dist1(d1), dist2(d2) {}
};
class AlgorithmData {
  public:
  AlgorithmData() {}
  virtual ~AlgorithmData() {
    ;
    for (Vehicle *p : vehicles) {
      if (p) {
        delete p;
      }
    }
    for (Grid *p : declaredGrid) {
      if (p) {
        delete p;
      }
    }
    ;
  }
  int numSol = 1;
  int numDivs = 0;
  const int MAX_ORDERS = 1024;
  std::vector<double> log = std::vector<double>(1 << 16);
  int numVertexes = 0, numEdges = 0, dayType = 0, numPatterns = 0, varEle = 0;
  int deltaEvent = 0, numGrids = 0;
  int numVehicles = 0;
  int tMax = 0, tDiv = 0, penaltyOutsideSupply = 0;
  int numSteps = 0;
  int penaltyOrder = 0, numOrders = 0;
  int pEvent = 0;
  std::vector<std::vector<int>> patternPredictedEnergyBalance;
  std::vector<Grid *> grids, vertexToGrid;
  std::vector<Vehicle *> vehicles;
  std::vector<Grid *> declaredGrid;
  size_t N_EV = 0, C_EV_init = 0, C_EV_max = 0, V_EV_max = 0, N_trans_max = 0,
         Delta_EV_move = 0;
  int disastertime = -1;
  std::vector<std::vector<std::pair<int, int>>> edges;
  const int VERY_LONG_DISTANCE = 100000;
};
struct dist_data {
  int u;
  int v;
  int distance;
};
bool operator==(const dist_data &dd1, const dist_data &dd2) {
  return dd1.u == dd2.u and dd1.v == dd2.v;
}
namespace std {
template <> struct hash<dist_data> {
  size_t operator()(const dist_data &dd) const {
    return (dd.u << 16) + dd.v;
  }
};
}
class Algorithm {
  public:
  AlgorithmData A_Data;
  Algorithm() {}
  ~Algorithm() { ; }
  virtual void init(const std::vector<vertex> &v);
  protected:
  std::vector<vertex> vertices;
  double xydist_to_edgedist;
  int distance_estimatoor(int v1, int v2) const;
  virtual void updateDistances();
  int dijkstra_distance(int v1, int v2) const;
  virtual void dijkstra(int v1);
  virtual std::vector<int> vec_dijkstra(int v1);
  template <class H> int A_star_distance(int v1, int v2, const H &h) const;
  int A_star_distance(int v1, int v2) const;
  virtual void printDistances();
  std::pair<std::vector<int>, std::vector<int>> A_star2(int v1, int v2) const;
  virtual void dumpGridsPerDistance();
};
static unsigned long long DijkstraNode_SeqCounter = 0;
class DijkstraNode {
  private:
  unsigned long long seq;
  public:
  int vertex;
  int distance = 0;
  DijkstraNode(int vertex) : vertex(vertex) { seq = DijkstraNode_SeqCounter++; }
  friend bool operator>(const DijkstraNode a, const DijkstraNode b) {
    if (a.distance > b.distance) {
      return true;
    } else if (a.distance < b.distance) {
      return false;
    } else {
      return (a.seq < b.seq);
    }
  }
};
void Algorithm::init(const std::vector<vertex> &v) {
  vertices = v;
  updateDistances();
  int cnt_id = 0;
  for (auto &v : A_Data.vehicles) {
    v->id = cnt_id++;
  }
}
int Algorithm::distance_estimatoor(int v1, int v2) const {
  return hypot(vertices[v1].x - vertices[v2].x,
               vertices[v1].y - vertices[v2].y) *
         xydist_to_edgedist;
}
void Algorithm::dijkstra(int v1) {
  ;
  exit(1);
}
template <class H>
int Algorithm::A_star_distance(int v1, int v2, const H &h) const {
  using namespace std;
  vector<int> dist(A_Data.numVertexes + 1, A_Data.VERY_LONG_DISTANCE);
  dist[v1] = 0;
  vector<bool> is_closed(A_Data.numVertexes + 1, false);
  priority_queue<DijkstraNode, vector<DijkstraNode>, greater<DijkstraNode>>
  candidate;
  DijkstraNode top(v1);
  top.distance = h(v1, v2);
  candidate.push(top);
  while (!candidate.empty()) {
    DijkstraNode top = candidate.top();
    candidate.pop();
    int pivot = top.vertex;
    if (pivot == v2)
      break;
    if (is_closed[pivot])
      continue;
    is_closed[pivot] = true;
    for (auto [v, d] : A_Data.edges[pivot]) {
      if (dist[pivot] + d < dist[v]) {
        dist[v] = dist[pivot] + d;
        DijkstraNode new_node(v);
        new_node.distance = dist[v] + h(v, v2);
        candidate.push(new_node);
      }
    }
  }
  return dist[v2];
}
int Algorithm::A_star_distance(int v1, int v2) const {
  using namespace std;
  vector<int> dist(A_Data.numVertexes + 1, A_Data.VERY_LONG_DISTANCE);
  dist[v1] = 0;
  vector<bool> is_closed(A_Data.numVertexes + 1, false);
  priority_queue<DijkstraNode, vector<DijkstraNode>, greater<DijkstraNode>>
  candidate;
  DijkstraNode top(v1);
  top.distance = distance_estimatoor(v1, v2);
  candidate.push(top);
  while (!candidate.empty()) {
    DijkstraNode top = candidate.top();
    candidate.pop();
    int pivot = top.vertex;
    if (pivot == v2)
      break;
    if (is_closed[pivot])
      continue;
    is_closed[pivot] = true;
    for (auto [v, d] : A_Data.edges[pivot]) {
      if (dist[pivot] + d < dist[v]) {
        dist[v] = dist[pivot] + d;
        DijkstraNode new_node(v);
        new_node.distance = dist[v] + distance_estimatoor(v, v2);
        candidate.push(new_node);
      }
    }
  }
  return dist[v2];
}
std::pair<std::vector<int>, std::vector<int>> Algorithm::A_star2(int v1,
                                                                 int v2) const {
  using namespace std;
  vector<int> dist(A_Data.numVertexes, A_Data.VERY_LONG_DISTANCE);
  vector<int> from(A_Data.numVertexes, -1);
  dist[v1] = 0;
  from[v1] = v1;
  vector<bool> is_closed(A_Data.numVertexes + 1, false);
  priority_queue<DijkstraNode, vector<DijkstraNode>, greater<DijkstraNode>>
  candidate;
  DijkstraNode top(v1);
  top.distance = distance_estimatoor(v1, v2);
  candidate.push(top);
  while (!candidate.empty()) {
    DijkstraNode top = candidate.top();
    candidate.pop();
    int pivot = top.vertex;
    if (pivot == v2)
      break;
    if (is_closed[pivot])
      continue;
    is_closed[pivot] = true;
    for (auto [v, d] : A_Data.edges[pivot]) {
      if (dist[pivot] + d < dist[v]) {
        dist[v] = dist[pivot] + d;
        from[v] = pivot;
        DijkstraNode new_node(v);
        new_node.distance = dist[v] + distance_estimatoor(v, v2);
        candidate.push(new_node);
      }
    }
  }
  return std::make_pair(dist, from);
}
std::vector<int> Algorithm::vec_dijkstra(int v1) {
  std::vector<int> dist(A_Data.numVertexes, A_Data.VERY_LONG_DISTANCE);
  dist[v1] = 0;
  std::priority_queue<DijkstraNode, std::vector<DijkstraNode>,
                      std::greater<DijkstraNode>>
  candidate;
  DijkstraNode top(v1);
  top.distance = 0;
  candidate.push(top);
  while (!candidate.empty()) {
    DijkstraNode top = candidate.top();
    candidate.pop();
    int pivot = top.vertex;
    if (dist[pivot] < top.distance) {
      continue;
    }
    for (auto [v, d] : A_Data.edges[pivot]) {
      if (dist[pivot] + d < dist[v]) {
        DijkstraNode new_node(v);
        new_node.distance = dist[v] = dist[pivot] + d;
        candidate.push(new_node);
      }
    }
  }
  return dist;
}
int Algorithm::dijkstra_distance(int v1, int v2) const {
  using namespace std;
  vector<int> dist(A_Data.numVertexes + 1, A_Data.VERY_LONG_DISTANCE);
  dist[v1] = 0;
  vector<bool> is_closed(A_Data.numVertexes + 1, false);
  priority_queue<DijkstraNode, vector<DijkstraNode>, greater<DijkstraNode>>
  candidate;
  DijkstraNode top(v1);
  top.distance = 0;
  candidate.push(top);
  while (!candidate.empty()) {
    DijkstraNode top = candidate.top();
    candidate.pop();
    int pivot = top.vertex;
    if (pivot == v2)
      break;
    if (is_closed[pivot])
      continue;
    is_closed[pivot] = true;
    for (auto [v, d] : A_Data.edges[pivot]) {
      if (dist[pivot] + d < dist[v]) {
        dist[v] = dist[pivot] + d;
        DijkstraNode new_node(v);
        new_node.distance = dist[v];
        candidate.push(new_node);
      }
    }
  }
  return dist[v2];
}
void Algorithm::updateDistances() {
  using namespace std;
  int maxDist = 0;
  if (is_first == 0) {
    is_first = 1;
    fprintf(stderr, "Start preprocess for graph (Dijkstra method) ");
    int indicator = 1;
    for (int i = 0; i < A_Data.numVertexes; i++) {
      if (i == indicator * A_Data.numVertexes / 20) {
        indicator++;
      }
      auto d = vec_dijkstra(i);
      for (int j = i + 1; j < A_Data.numVertexes; j++) {
        maxDist = std::max(maxDist, d[j]);
      }
    }
    int x_min = 60000, x_max = -60000, y_min = 60000, y_max = -60000;
    for (auto &vertex : vertices)
      x_min = std::min(x_min, vertex.x), x_max = std::max(x_max, vertex.x),
      y_min = std::min(y_min, vertex.y), y_max = std::max(y_max, vertex.y);
    xydist_to_edgedist =
    1.0 * maxDist / ((x_max - x_min) + (y_max - y_min)) * 1.1;
    ;
    maxDist++;
  }
}
void Algorithm::printDistances() {
  ;
  exit(1);
}
void Algorithm::dumpGridsPerDistance() {
}
class Main : public Algorithm {
  public:
  static void main(std::vector<std::string> &args);
  Main() {
    for (size_t i = 0; i < A_Data.log.size(); i++) {
      A_Data.log[i] = std::log((i + 0.5) / A_Data.log.size());
    }
  }
  ~Main() { ; }
  public:
  int dist(int v1, int v2);
  int dist(int v1, int v2, int &next);
  int dist(Vehicle *v, int vertex);
};
int Main::dist(int v1, int v2) {
  int dummy;
  return dist(v1, v2, dummy);
}
int Main::dist(int v1, int v2, int &next) {
  using namespace std;
  static std::list<dist_data> dist_cache;
  static std::unordered_map<dist_data, std::list<dist_data>::iterator>
  cache_reference;
  static size_t called = 0;
  static size_t cache_miss = 0;
  ++called;
  const size_t cache_size = 4 * A_Data.numVertexes;
  dist_data key{v1, v2, 0};
  if (cache_reference.count(key) == 0) {
    cache_miss++;
    ;
    key.distance = A_star_distance(v1, v2);
    if (dist_cache.size() > cache_size) {
      cache_reference.erase(dist_cache.back());
      dist_cache.pop_back();
    }
  } else {
    key.distance = cache_reference[key]->distance;
    dist_cache.erase(cache_reference[key]);
  }
  if (called % 50000 == 0)
   
                     ;
  dist_cache.push_front(key);
  cache_reference[key] = dist_cache.begin();
  return key.distance;
}
int Main::dist(Vehicle *v, int vertex) {
  if (v->vertex1 == v->vertex2) {
    return dist(v->vertex1, vertex);
  }
  return std::min(dist(v->vertex1, vertex) + v->dist1,
                  dist(v->vertex2, vertex) + v->dist2);
}
extern bool outlog;
const char TEXT_budget[] = "budget";
const char TEXT_seed[] = "seed";
const char TEXT_temporal[] = "temporal";
const char TEXT_score[] = "score";
const char TEXT_graph[] = "graph";
const char TEXT_demand[] = "demand";
const char TEXT_radiation[] = "radiation";
const char TEXT_asset[] = "asset";
const char TEXT_order[] = "order";
const char TEXT_shelter[] = "shelter";
const char TEXT_work[] = "work";
const char TEXT_end[] = "end";
const char TEXT_PV[] = "PV";
const char TEXT_FE[] = "FE";
const char TEXT_RB[] = "RB";
const char TEXT_EVC[] = "EVC";
const char TEXT_vehicle[] = "vehicle";
const unsigned int RANDOM_SEED = 999999;
class StatusOnAcc {
  public:
  bool acc_mode = false;
  size_t Day_acc = 0;
  size_t T_acc = 0;
  std::vector<int> grid_cap;
  std::vector<int> vehicle_cap;
  std::vector<position> vehicle_pos;
  std::vector<int> work_cap;
  StatusOnAcc(size_t day_acc, size_t t_acc) : Day_acc(day_acc), T_acc(t_acc) {}
};
class Command2 {
  public:
  std::string group;
  int id;
  std::string command;
  int param1;
};
class WorkDetail {
  public:
  int x;
  int delta_work;
  int I_work_min;
  int D_work;
  int Cap_work_ele;
  int V_work_charge;
  int V_work_discharge;
  int Eta_work;
  std::vector<int> A_work;
};
class WorkStatus {
  public:
  int id;
  int charge;
  int yield;
  int startTime;
  const WorkDetail *detail;
  WorkStatus(int id, const WorkDetail *detail) : id(id), detail(detail) {
    charge = 0;
    yield = 0;
    startTime = -1;
  }
};
class Work {
  public:
  size_t N_work;
  std::vector<std::vector<WorkDetail>> demands;
  std::vector<WorkStatus> status;
};
class judge {
  public:
  virtual ~judge() {
    if (outlog_fp) {
      fclose(outlog_fp);
    }
  }
  FILE *outlog_fp = NULL;
  std::vector<vertex> v;
  std::vector<int> v_p;
  graph<edge> g;
  std::vector<vehicle> vehicles;
  std::vector<std::vector<energy>> energies;
  int C_init = 0;
  int C_total = 0;
  size_t N, M;
  size_t Daytype = 0, N_nano;
  size_t N_vehicle;
  size_t T_now;
  const size_t N_sol = 1;
  size_t T_grace = 0;
  size_t T_last;
  size_t T_max;
  size_t N_div, N_day, N_acc, N_pattern, sigma_ele = 0;
  size_t Delta_event = 0;
  double p_event = 0.0;
  std::vector<std::vector<double>> pw;
  size_t P_trans = 100000;
  double Gamma = 2;
  size_t N_demand = 0;
  Work work;
  std::vector<size_t> u_output, v_output, c_output;
  std::vector<size_t> x_output, type_output, C_Grid_init_output,
  C_Grid_max_output, c_max_output, c_init_output;
  std::vector<size_t> pos_output, EV_init_output, EV_max_output;
  std::stack<energy> info_day;
  unsigned long int sum_out_charge = 0;
  size_t &V = N;
  size_t &E = M;
  std::vector<std::string> s;
  std::istringstream instream;
  std::string StrLine;
  score2 curr_score;
  Demand demand;
  radiation rad;
  shelter shlt;
  std::vector<in_order> in_orders;
  std::vector<std::vector<OrderB>> allOrders;
  std::vector<OrderB *> activeOrders;
  int p_trans_const;
  std::vector<int> pw_error;
  std::random_device pw_error_rd{};
  std::mt19937 pw_error_gen{pw_error_rd()};
  inline void setPWerrorGenSeed(unsigned int seed) { pw_error_gen.seed(seed); }
  asset Asset;
  grid_info Grid_Info;
  EV_info ev_info;
  double env_fuel;
  double env_buy;
  double acc_factor;
  void open_outlog();
  double calc_day_score(size_t day,
                        double trans_score,
                        double ele_score,
                        double env_score,
                        double work_score);
  double work_score();
  double transport_score_2HC2020();
  double transport_score(Main &main);
  double electricity_score_2HC2020();
  double current_electricity_score();
  double electricity_score(double C_balance, double es);
  double current_all_grid_charge();
  double current_all_EV_charge(Main &main);
  double current_all_EV_return(Main &main);
  double current_env_score();
  void init_input(FILE *fp);
  bool valid_move(size_t id, size_t v);
  bool valid_pickup(size_t order_id, size_t vehicle_id);
  bool next_time_step();
  void getCommands(std::vector<Command2> &commands);
  void do_judge(Main &main, std::vector<Command2> &commands, bool onAcc);
  bool readInput1(FILE *fp);
  void readInput2(FILE *fp);
  bool checkRange(const int val,
                  const int lbound,
                  const bool lboundEqu,
                  const int ubound,
                  const bool uboundEqu) {
    if (lboundEqu) {
      if (uboundEqu) {
        return (val >= lbound && val <= ubound);
      } else {
        return (val >= lbound && val < ubound);
      }
    } else {
      if (uboundEqu) {
        return (val > lbound && val <= ubound);
      } else {
        return (val > lbound && val < ubound);
      }
    }
  }
  bool checkInList(const int val, const std::vector<int> valList) {
    for (const auto &v : valList) {
      if (v == val) {
        return true;
      }
    }
    return false;
  }
  std::string set_Algorithm_Initial_Input1(const bool submitFlag,
                                           const size_t day,
                                           std::vector<std::string> &args,
                                           Main &main,
                                           StatusOnAcc *acc_stat);
  int set_Algorithm_Initial_Input2(const bool submitFlag,
                                   Main &main,
                                   const size_t day,
                                   bool ignore_order);
  void dumpTo2020InputFile(const Main &main);
  void dumpForDebuggingScore(std::ofstream &ev1,
                             std::ofstream &ev2,
                             std::ofstream &grid1,
                             std::ofstream &grid2,
                             const bool submitFlag,
                             const Main &main,
                             const size_t &t,
                             const size_t day);
  int createNanoGrid(const size_t day);
  void output3(const Main &main, std::ostream &dest, bool comment);
  std::string run_Algorithm(const bool submitFlag,
                            Main &main,
                            const size_t &time,
                            const size_t day,
                            bool onAcc);
  bool readLineSkipComment();
  std::string getLine(FILE *fp);
  std::string getLineFromStdIn();
  std::string processQueryCommand(const std::string &cmd, FILE *fp);
  void getBudgetData(FILE *);
  std::string setBudgetData(FILE *fp);
  void getSeedData(FILE *);
  void getTemporalData(FILE *);
  std::string setTemporalData(FILE *fp);
  void getScoreData(FILE *);
  std::string setScoreData(FILE *fp);
  void getGraphData(FILE *);
  std::string setGraphData(FILE *fp);
  void getDemandData(FILE *);
  std::string setDemandData(FILE *fp, int day, int id);
  void getAssetData(FILE *);
  std::string setAssetData(FILE *fp, const std::string &arg2, int id);
  void setAssetPV(FILE *fp, int id);
  void setAssetFE(FILE *fp, int id);
  void setAssetRB(FILE *fp, int id);
  void setAssetEVC(FILE *fp, int id);
  void setAssetV(FILE *fp, int id);
  void getInOrderData(FILE *);
  std::string setInOrderData(FILE *fp, int day);
  void getShelterData(FILE *);
  std::string setShelterData(FILE *fp);
  void getRadiationData(FILE *);
  std::string setRadiationData(FILE *fp, int day, int id);
  std::vector<double>
  calcRadRValue(int day, int id, const RadiationCalcType &calcType);
  void getWorkData(FILE *);
  std::string setWorkData(FILE *fp, int day, int id);
  int calc_pw_error(const size_t day, const size_t id);
  inline double distance2D(const double x1,
                           const double y1,
                           const double x2,
                           const double y2) {
    return hypot(x2 - x1, y2 - y1);
  }
  void getGridInfoData(FILE *fp);
  void getEVInfoData(FILE *fp);
  const grid_info_data &vertexToGridInfoData(size_t v_id) const;
  const grid_info_data &emptyGridInfoData() const;
  void createOrders(size_t day, bool ignore_order);
  void saveStat(StatusOnAcc &);
  bool checkBuy();
  private:
  int sample_vertex(const std::vector<int> &selection_table,
                    int normalizing_constant,
                    std::mt19937_64 &engine);
  void create_orders(const std::vector<int> &o,
                     const std::vector<int> &p,
                     std::mt19937_64 &engine,
                     std::vector<OrderB> &todayOrders);
};
bool judge::valid_move(size_t id, size_t vertex) {
  ;
  size_t Delta_move = vehicles[id].delta_move;
  position pos = vehicles[id].pos;
  if (pos.on_vertex()) {
    size_t now = pos.to;
    if (pos.distance == 0) {
      now = pos.from;
    }
    int edge_id = g.find(now, vertex);
    if (edge_id == -1) {
      ;
      return false;
    } else {
      if (!vehicles[id].consume(Delta_move))
        return true;
      edge e = g[now][edge_id];
      position next(now, vertex, 1, e.cost);
      vehicles[id].set_position(next);
    }
  } else {
    if (pos.from == vertex) {
      if (!vehicles[id].consume(Delta_move))
        return true;
      vehicles[id].pos.distance--;
    } else if (pos.to == vertex) {
      if (!vehicles[id].consume(Delta_move))
        return true;
      vehicles[id].pos.distance++;
    } else {
      ;
      return false;
    }
  }
  if (vehicles[id].pos.on_vertex()) {
    ;
    ;
    for (auto it = vehicles[id].orders.begin(); it != vehicles[id].orders.end();
  ) {
      int oid = *it;
      ;
      OrderB *o = activeOrders[oid];
      if (o->status == 2 &&
          o->dest == vehicles[id].now_vertex()) {
        o->endTime = T_now;
        o->status = 3;
        it = vehicles[id].orders.erase(it);
 ;
      }else{
       it++;
      }
    }
    ;
  }
  return true;
}
bool judge::valid_pickup(size_t order_id, size_t vehicle_id) {
  if (order_id < 0 || order_id >= activeOrders.size()) {
    ;
    return false;
  }
  OrderB *o = activeOrders[order_id];
  if (o->status != 1) {
    ;
    return false;
  }
  auto &v = vehicles[vehicle_id];
  ;
  ;
  if (v.orders.size() >= (size_t)v.N_Max_Trans) {
    ;
    ;
    ;
    return false;
  }
  assert(o->vehicle_id == -1);
  if (v.now_vertex() != o->orig) {
    ;
    ;
    ;
    return false;
  }
  vehicles[vehicle_id].add_order(order_id);
  o->vehicle_id = vehicle_id;
  o->status = 2;
  return true;
}
pid_t __reactive_pid;
int __reactive_input, __reactive_output;
int __standard_input = -1;
int __standard_output = -1;
bool is_connected = false;
int reactive_start(int, char *const *argv) {
  ;
  int pipe_c2p[2], pipe_p2c[2];
  signal(SIGPIPE, SIG_IGN);
  if (pipe(pipe_c2p) < 0 || pipe(pipe_p2c) < 0) {
    fprintf(stderr, "pipe: failed to open pipes\n");
    return 1;
  }
  if ((__reactive_pid = fork()) < 0) {
    fprintf(stderr, "fork: failed to fork\n");
    return 1;
  }
  ;
  if (__reactive_pid == 0) {
    close(pipe_p2c[1]);
    close(pipe_c2p[0]);
    dup2(pipe_p2c[0], 0);
    dup2(pipe_c2p[1], 1);
    close(pipe_p2c[0]);
    close(pipe_c2p[1]);
    system(argv[1]);
    exit(1);
  }
  close(pipe_p2c[0]);
  close(pipe_c2p[1]);
  __reactive_input = pipe_p2c[1];
  __reactive_output = pipe_c2p[0];
  return 0;
}
void reactive_connect() {
  if (is_connected)
    return;
  if (__standard_input == -1)
    __standard_input = dup(0);
  if (__standard_output == -1)
    __standard_output = dup(1);
  dup2(__reactive_input, 1);
  dup2(__reactive_output, 0);
  is_connected = true;
}
void reactive_disconnect() {
  if (!is_connected)
    return;
  fflush(stdout);
  dup2(__standard_input, 0);
  dup2(__standard_output, 1);
  is_connected = false;
}
void reactive_end() {
  int status;
  close(__reactive_input);
  sleep(1);
  if (kill(__reactive_pid, 0) == 0) {
    kill(__reactive_pid, SIGKILL);
  }
  waitpid(__reactive_pid, &status, WUNTRACED);
}
void reactive_write(std::string buf) {
  write(__reactive_input, buf.c_str(), buf.size());
}
std::string reactive_read(size_t max_len = 100000) {
  static char buf[1024];
  static int len = 0;
  std::string result;
  while (result.size() < max_len) {
    if (!len) {
      len = read(__reactive_output, buf,
                 std::min(1000, (int)(max_len - result.size())));
      if (!len)
        return result;
    }
    char *pos = (char *)memchr(buf, '\n', len);
    if (pos) {
      result += std::string(buf, pos - buf + 1);
      memmove(buf, pos + 1, len - (pos + 1 - buf));
      len -= pos - buf + 1;
      return result;
    } else {
      result += std::string(buf, len);
      len = 0;
    }
  }
  return result;
}
static struct _tag_guard {
  bool is_accepted = false;
  ~_tag_guard() {
    if (is_connected)
      reactive_disconnect();
    if (!is_accepted)
      std::cout << -99999999 << "\n";
  }
} guard;
using namespace std;
int SUBMIT_SEED = 0;
RandomHelper random_helper(RANDOM_SEED);
bool outlog = false;
void judge::open_outlog() {
  if (!outlog) {
    return;
  }
  char fname[1024];
  time_t rawtime;
  struct tm *timeinfo;
  time(&rawtime);
  timeinfo = localtime(&rawtime);
  strftime(fname, sizeof(fname), "outlog_%Y%m%d_%H%M%S.log", timeinfo);
  outlog_fp = fopen(fname, "w");
}
double judge::calc_day_score(size_t day,
                             double trans_score,
                             double ele_score,
                             double env_score,
                             double work_score) {
  double score = 0.0;
  score += curr_score.w_trans * trans_score;
  score += curr_score.w_ele * ele_score;
  score += curr_score.w_env * env_score;
  score += curr_score.w_work * work_score;
  score *= curr_score.w_days[day];
  return score;
}
double judge::work_score() {
  double score = 0;
  int Work_cnt = 0;
  for (auto &w : work.status) {
    if (w.yield >= w.detail->D_work) {
      Work_cnt++;
    }
  }
  score += curr_score.alpha_work * Work_cnt;
  return score;
}
double judge::transport_score(Main &main) {
  ;
  double score = 0.0;
  int N_canceled = 0;
  int N_undelivered = 0;
  for (OrderB *o : activeOrders) {
    double T_wait = (o->endTime - o->startTime);
    if (o->status == 3) {
      double dist = main.dist(o->orig, o->dest);
      double T_i = dist;
      double sc =
      curr_score.alpha_trans_fee * dist -
      curr_score.alpha_trans_penalty * (T_wait - T_i) * (T_wait - T_i);
      ;
      score += std::max(0.0, sc);
    } else if (o->status == -2) {
      N_canceled++;
    } else if (o->status == 1 || o->status == 2)
      N_undelivered++;
  }
  ;
  score -= curr_score.alpha_trans_canceled * N_canceled;
  score -= curr_score.alpha_trans_undelivered * N_undelivered;
  return score;
}
double judge::electricity_score_2HC2020() {
  double score = 0;
  for (vehicle v : vehicles) {
    score += v.cap;
  }
  for (node n : g.nodes) {
    score += n.cap;
  }
  score -= Gamma * sum_out_charge;
  return score;
}
double judge::current_electricity_score() {
  double score = 0.0;
  for (size_t j = 0; j < g.nodes.size(); j++) {
    score -= curr_score.alpha_ele_FE * g.nodes[j].L_FE +
             curr_score.alpha_ele_buy * g.nodes[j].L_buy;
  }
  return score;
}
double judge::electricity_score(double C_balance, double daily_sum) {
  double score = 0.0;
  score += curr_score.alpha_ele * C_balance + daily_sum;
  return score;
}
double judge::current_all_grid_charge() {
  double charge = 0.0;
  for (size_t j = 0; j < g.nodes.size(); j++) {
    charge += g.nodes[j].cap;
  }
  return charge;
}
double judge::current_all_EV_charge(Main &main) {
  double charge = 0.0;
  for (size_t j = 0; j < main.A_Data.vehicles.size(); j++) {
    charge += main.A_Data.vehicles[j]->charge;
  }
  return charge;
}
double judge::current_all_EV_return(Main &main) {
  double charge = 0.0;
  for (size_t j = 0; j < main.A_Data.vehicles.size(); j++) {
    Vehicle *v = main.A_Data.vehicles[j];
    double ret = main.dist(v, v->vertex0);
    charge += v->Delta_move * ret;
  }
  return charge;
}
double judge::current_env_score() {
  double score = 0.0;
  for (size_t j = 0; j < g.nodes.size(); j++) {
    score -= curr_score.alpha_env_fuel * g.nodes[j].L_FE +
             curr_score.alpha_env_buy * g.nodes[j].L_buy;
  }
  return score;
}
bool judge::next_time_step() {
  for (auto &o : allOrders[T_now]) {
    activeOrders.push_back(&o);
    do { if (!((size_t)o.orig < V)) exit(1); } while (0);
    do { if (!((size_t)o.dest < V)) exit(1); } while (0);
  }
  if (false) fprintf(stderr, "###Debug %s(%d),energies.size=%zu\n", "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp",
                      223, energies.size());
  for (size_t i = 0; i < N_nano; i++) {
    info_day.push(energies[T_now][i]);
  }
  T_now++;
  if (T_now > T_last) {
    return false;
  }
  return true;
}
bool judge::readInput1(FILE *fp) {
  ;
  bool sts = false;
  for (;;) {
    if ((sts = readLineSkipComment())) {
      ;
      if (s[0] == TEXT_budget) {
        getBudgetData(fp);
      } else if (s[0] == TEXT_seed) {
        getSeedData(fp);
      } else if (s[0] == TEXT_temporal) {
        getTemporalData(fp);
      } else if (s[0] == TEXT_score) {
        getScoreData(fp);
      } else if (s[0] == TEXT_graph) {
        getGraphData(fp);
      } else if (s[0] == TEXT_demand) {
        getDemandData(fp);
      } else if (s[0] == TEXT_radiation) {
        getRadiationData(fp);
      } else if (s[0] == TEXT_asset) {
        getAssetData(fp);
      } else if (s[0] == TEXT_order) {
        getInOrderData(fp);
      } else if (s[0] == TEXT_shelter) {
        getShelterData(fp);
      } else if (s[0] == TEXT_work) {
        getWorkData(fp);
        break;
      } else {
        ;
        exit(1);
      }
    } else {
      ;
      return sts;
    }
  }
  sts = true;
  return sts;
}
void judge::readInput2(FILE *fp) {
  C_total = 0;
  getGridInfoData(fp);
  getEVInfoData(fp);
}
void judge::getGridInfoData(FILE *) {
  Grid_Info.data_list.clear();
  Grid_Info.N_grid = 0;
  readLineSkipComment();
  size_t n = 0;
  try {
    n = std::stoi(s[0]);
  } catch (std::exception &e) {
    std::cerr << "exception caught: " << e.what() << '\n';
    exit(1);
  }
  Grid_Info.init(n);
  ;
  size_t i;
  for (i = 0; i < n; i++) {
    ;
    auto &grid_data = Grid_Info.data_list[i];
    readLineSkipComment();
    if (s.size() == 2) {
      grid_data.x_grid_pos = std::stoi(s[0]) - 1;
      grid_data.chg_grid_init = std::stoi(s[1]);
      if (!(0 <= grid_data.x_grid_pos and grid_data.x_grid_pos < V)) {
        ;
        break;
      }
    } else {
      break;
    }
    readLineSkipComment();
    if (s.size() == 2) {
      grid_data.type_grid_PV = std::stoi(s[0]) - 1;
      grid_data.A_grid_PV = std::stoi(s[1]);
      if (!(0 <= grid_data.type_grid_PV and
            grid_data.type_grid_PV < Asset.N_PV)) {
        ;
        exit(1);
      }
      if (!(0 <= grid_data.A_grid_PV)) {
        ;
        exit(1);
      }
      do { if (grid_data.A_grid_PV < 0 or 500 < grid_data.A_grid_PV) { ; ; ; ; exit(1); } } while (0);
      auto pv = Asset.getPVinfo(grid_data.type_grid_PV);
      int PV_area = grid_data.A_grid_PV * pv->A_PV;
      int grid_area = this->v[grid_data.x_grid_pos].A;
      if (PV_area > grid_area) {
        ;
        exit(1);
      }
      int C_PV = grid_data.A_grid_PV * pv->C_PV_init +
                 grid_data.A_grid_PV * pv->A_PV * v[grid_data.x_grid_pos].l;
      ;
      this->C_total += C_PV;
      do { if (this->C_total < 0 or 1000000000 < this->C_total) { ; ; ; ; exit(1); } } while (0);
    } else {
      break;
    }
    readLineSkipComment();
    if (s.size() == 1) {
      grid_data.type_grid_FE = std::stoi(s[0]) - 1;
      if (!(0 <= grid_data.type_grid_FE and
            grid_data.type_grid_FE < Asset.N_FE)) {
        ;
        exit(1);
      }
      auto fe = Asset.getFEinfo(grid_data.type_grid_FE);
      int C_FE = fe->C_FE_init;
      ;
      this->C_total += C_FE;
      do { if (this->C_total < 0 or 1000000000 < this->C_total) { ; ; ; ; exit(1); } } while (0);
    } else {
      break;
    }
    readLineSkipComment();
    if (s.size() == 2) {
      grid_data.type_grid_RB = std::stoi(s[0]) - 1;
      grid_data.A_grid_RB = std::stoi(s[1]);
      if (!(0 <= grid_data.type_grid_RB and
            grid_data.type_grid_RB < Asset.N_RB)) {
        ;
        exit(1);
      }
      if (!(0 <= grid_data.A_grid_RB)) {
        ;
        exit(1);
      }
      if (!(0 <= grid_data.chg_grid_init and
            grid_data.chg_grid_init <=
            Asset.RB_list[grid_data.type_grid_RB].Cap_RB *
            grid_data.A_grid_RB)) {
       
                                                                           ;
        exit(1);
      }
      do { if (grid_data.A_grid_RB < 0 or 10000 < grid_data.A_grid_RB) { ; ; ; ; exit(1); } } while (0);
      auto rb = Asset.getRBinfo(grid_data.type_grid_RB);
      int C_RB = grid_data.A_grid_RB * rb->C_RB_init;
      ;
      this->C_total += C_RB;
      do { if (this->C_total < 0 or 1000000000 < this->C_total) { ; ; ; ; exit(1); } } while (0);
    } else {
      break;
    }
    readLineSkipComment();
    if (s.size() == 1) {
      grid_data.type_grid_EVC = std::stoi(s[0]) - 1;
      if (!(0 <= grid_data.type_grid_EVC and
            grid_data.type_grid_EVC < Asset.N_EVC)) {
        ;
        exit(1);
      }
      auto evc = Asset.getEVCinfo(grid_data.type_grid_EVC);
      int C_EVC = evc->C_EVC_init;
      ;
      this->C_total += C_EVC;
      do { if (this->C_total < 0 or 1000000000 < this->C_total) { ; ; ; ; exit(1); } } while (0);
    } else {
      break;
    }
  }
  if (i != n) {
    exit(1);
  }
}
void judge::getEVInfoData(FILE *) {
  size_t n;
  readLineSkipComment();
  try {
    n = std::stoi(s[0]);
  } catch (std::exception &e) {
    std::cerr << "exception caught: " << e.what() << '\n';
    exit(1);
  }
  N_vehicle = n;
  ev_info.init(n);
  size_t i;
  for (i = 0; i < n; i++) {
    readLineSkipComment();
    if (s.size() == 3) {
      ev_info.data_list[i].x_EV_pos = std::stoi(s[0]) - 1;
      ev_info.data_list[i].Chg_EV_init = std::stoi(s[1]);
      ev_info.data_list[i].type_EV = std::stoi(s[2]) - 1;
      if (!(0 <= ev_info.data_list[i].x_EV_pos and
            ev_info.data_list[i].x_EV_pos < V)) {
        ;
        break;
      }
      if (!(0 <= ev_info.data_list[i].type_EV and
            ev_info.data_list[i].type_EV < Asset.N_V)) {
        ;
        break;
      }
      if (!(0 <= ev_info.data_list[i].Chg_EV_init and
            ev_info.data_list[i].Chg_EV_init <=
            Asset.V_list[ev_info.data_list[i].type_EV].Cap_V_ele)) {
       
                                                                   ;
        break;
      }
      auto &ev = Asset.V_list[ev_info.data_list[i].type_EV];
      int C_EV = ev.C_V_init;
      ;
      this->C_total += C_EV;
      do { if (this->C_total < 0 or 1000000000 < this->C_total) { ; ; ; ; exit(1); } } while (0);
      bool valid_x_EV_pos = false;
      for (const auto &gid : Grid_Info.data_list)
        if (gid.x_grid_pos == ev_info.data_list[i].x_EV_pos)
          valid_x_EV_pos = true;
      do { if (!(valid_x_EV_pos)) exit(1); } while (0);
    } else {
      break;
    }
  }
  if (i != n) {
    exit(1);
  }
}
std::string judge::getLine(FILE *fp) {
  std::string result = "";
  char *line = nullptr;
  size_t len = 0;
  getline(&line, &len, fp);
  if (line) {
    result = std::string(line);
    free(line);
    line = nullptr;
    std::vector<std::string> v;
    int c = StringHelper::SplitToken(result, "\r\n", v);
    if (c > 0) {
      result = v[0];
    } else {
      result = "";
    }
  }
  return result;
}
std::string judge::getLineFromStdIn() {
  std::string result = "";
  std::getline(std::cin, result);
  if (false) fprintf(stderr, "###Debug getLineFromStdIn, result=(%s)\n",
                      result.c_str());
  return result;
}
std::string judge::processQueryCommand(const std::string &cmd, FILE *fp) {
  if (false) fprintf(stderr, "###Debug >>>processQueryCommand(%s)\n",
                      cmd.c_str());
  ;
  std::string ret = "WA";
  std::vector<std::string> cmd_args;
  int argc = StringHelper::SplitToken(cmd, " ", cmd_args);
  if (cmd_args[0] == TEXT_budget) {
    ret = setBudgetData(fp);
  } else if (cmd_args[0] == TEXT_temporal) {
    ret = setTemporalData(fp);
  } else if (cmd_args[0] == TEXT_score) {
    ret = setScoreData(fp);
  } else if (cmd_args[0] == TEXT_graph) {
    ret = setGraphData(fp);
  } else if (cmd_args[0] == TEXT_demand) {
    int day = -1;
    int id = -1;
    if (argc >= 3) {
      day = std::stoi(cmd_args[1]);
      if (!checkRange(day, 1, true, N_day, true)) {
        if (false) fprintf(stderr, "###Debug invalid day in command:%s\n",
                            cmd.c_str());
        exit(1);
      }
      day -= 1;
      id = std::stoi(cmd_args[2]);
      if (!checkRange(id, 1, true, N_demand, true)) {
        if (false) fprintf(stderr, "###Debug invalid id in command:%s\n",
                            cmd.c_str());
        exit(1);
      }
      id -= 1;
    }
    ret = setDemandData(fp, day, id);
  } else if (cmd_args[0] == TEXT_radiation) {
    int day = -1;
    int id = -1;
    if (argc >= 3) {
      day = std::stoi(cmd_args[1]);
      if (!checkRange(day, 1, true, N_day, true)) {
        if (false) fprintf(stderr, "###Debug invalid day in command:%s\n",
                            cmd.c_str());
        exit(1);
      }
      day -= 1;
      id = std::stoi(cmd_args[2]);
      if (!checkRange(id, 1, true, V, true)) {
        if (false) fprintf(stderr, "###Debug invalid id in command:%s\n",
                            cmd.c_str());
        exit(1);
      }
      id -= 1;
    } else {
      ;
      exit(1);
    }
    ret = setRadiationData(fp, day, id);
  } else if (cmd_args[0] == TEXT_asset) {
    std::string arg2 = "";
    int id = 0;
    if (argc == 3) {
      arg2 = cmd_args[1];
      id = std::stoi(cmd_args[2]);
    } else if (argc == 2) {
      arg2 = cmd_args[1];
    }
    if (argc == 3) {
      if (arg2 == TEXT_PV) {
        if (!checkRange(id, 1, true, Asset.N_PV, true)) {
          if (false) fprintf(stderr, "###Debug invalid id in command:%s\n",
                              cmd.c_str());
          exit(1);
        }
      } else if (arg2 == TEXT_FE) {
        if (!checkRange(id, 1, true, Asset.N_FE, true)) {
          if (false) fprintf(stderr, "###Debug invalid id in command:%s\n",
                              cmd.c_str());
          exit(1);
        }
      } else if (arg2 == TEXT_RB) {
        if (!checkRange(id, 1, true, Asset.N_RB, true)) {
          if (false) fprintf(stderr, "###Debug invalid id in command:%s\n",
                              cmd.c_str());
          exit(1);
        }
      } else if (arg2 == TEXT_EVC) {
        if (!checkRange(id, 1, true, Asset.N_EVC, true)) {
          if (false) fprintf(stderr, "###Debug invalid id in command:%s\n",
                              cmd.c_str());
          exit(1);
        }
      } else if (arg2 == TEXT_vehicle) {
        if (!checkRange(id, 1, true, Asset.N_V, true)) {
          if (false) fprintf(stderr, "###Debug invalid id in command:%s\n",
                              cmd.c_str());
          exit(1);
        }
      }
    }
    id -= 1;
    ret = setAssetData(fp, arg2, id);
  } else if (cmd_args[0] == TEXT_order) {
    int day = -1;
    if (argc >= 2) {
      day = std::stoi(cmd_args[1]);
      if (!checkRange(day, 1, true, N_day, true)) {
        if (false) fprintf(stderr, "###Debug invalid day in command:%s\n",
                            cmd.c_str());
        exit(1);
      }
      day -= 1;
    }
    ret = setInOrderData(fp, day);
  } else if (cmd_args[0] == TEXT_shelter) {
    ret = setShelterData(fp);
  } else if (cmd_args[0] == TEXT_work) {
    int day;
    int id;
    if (argc == 3) {
      day = std::stoi(cmd_args[1]);
      if (!checkRange(day, 1, true, N_day, true)) {
        if (false) fprintf(stderr, "###Debug invalid day in command:%s\n",
                            cmd.c_str());
        exit(1);
      }
      day -= 1;
      id = std::stoi(cmd_args[2]);
      if (!checkRange(id, 1, true, work.N_work, true)) {
        if (false) fprintf(stderr, "###Debug invalid id in command:%s\n",
                            cmd.c_str());
        exit(1);
      }
      id -= 1;
    } else if (argc == 1) {
      day = -1;
      id = -1;
    } else {
      exit(1);
    }
    ret = setWorkData(fp, day, id);
  } else if (cmd_args[0] == TEXT_end) {
    ret = TEXT_end;
  } else {
    if (false) fprintf(stderr, "###Debug invalid query command:%s\n",
                        cmd.c_str());
    exit(1);
  }
  if (false) fprintf(stderr, "###Debug <<<processQueryCommand(%s)\n",
                      cmd.c_str());
  return ret;
}
void judge::getBudgetData(FILE *) {
  readLineSkipComment();
  C_init = std::stoi(s[0]);
}
std::string judge::setBudgetData(FILE *fp) {
  std::string ret = "OK";
  { if (fp != outlog_fp) { fprintf(fp, "%d\n", C_init); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d\n", C_init); } };
  return ret;
}
void judge::getSeedData(FILE *) {
  ;
  readLineSkipComment();
  ;
  SUBMIT_SEED = std::stoi(s[0]);
}
void judge::getTemporalData(FILE *) {
  ;
  readLineSkipComment();
  T_max = std::stoi(s[0]);
  T_last = std::stoi(s[1]);
  N_div = std::stoi(s[2]);
  N_day = std::stoi(s[3]);
  N_acc = std::stoi(s[4]);
  T_grace = std::stoi(s[5]);
  if (false) fprintf(
  stderr,
  "###Debug T_max=%zu,T_last=%zu,N_div=%zu,N_day=%zu,N_acc=%zu,T_grace=%zu\n",
  T_max, T_last, N_div, N_day, N_acc, T_grace);
}
std::string judge::setTemporalData(FILE *fp) {
  std::string ret = "OK";
  { if (fp != outlog_fp) { fprintf(fp, "%zu %zu %zu %zu %zu %zu\n", T_max, T_last, N_div, N_day, N_acc, T_grace); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu %zu %zu %zu %zu %zu\n", T_max, T_last, N_div, N_day, N_acc, T_grace); } }
                                          ;
  return ret;
}
void judge::getScoreData(FILE *) {
  ;
  readLineSkipComment();
  curr_score.alpha_cost = std::stoi(s[0]);
  readLineSkipComment();
  curr_score.w_days.resize(N_day);
  for (size_t i = 0; i < N_day; i++) {
    curr_score.w_days[i] = std::stoi(s[i]);
  }
  readLineSkipComment();
  curr_score.w_trans = std::stod(s[0]);
  curr_score.w_ele = std::stod(s[1]);
  curr_score.w_env = std::stod(s[2]);
  curr_score.w_acc = std::stod(s[3]);
  curr_score.w_work = std::stod(s[4]);
  readLineSkipComment();
  do { if ((s.size()) != (4)) { ; ; ; exit(1); } } while (0);
  curr_score.alpha_trans_fee = std::stod(s[0]);
  curr_score.alpha_trans_penalty = std::stod(s[1]);
  curr_score.alpha_trans_canceled = std::stod(s[2]);
  curr_score.alpha_trans_undelivered = std::stod(s[3]);
  readLineSkipComment();
  curr_score.alpha_ele = std::stod(s[0]);
  curr_score.alpha_ele_FE = std::stod(s[1]);
  curr_score.alpha_ele_buy = std::stod(s[2]);
  readLineSkipComment();
  curr_score.alpha_env = std::stod(s[0]);
  curr_score.alpha_env_fuel = std::stod(s[1]);
  curr_score.alpha_env_buy = std::stod(s[2]);
  readLineSkipComment();
  curr_score.alpha_acc = std::stoi(s[0]);
  readLineSkipComment();
  curr_score.alpha_work = std::stoi(s[0]);
}
std::string judge::setScoreData(FILE *fp) {
  std::string ret = "OK";
  { if (fp != outlog_fp) { fprintf(fp, "%d\n", curr_score.alpha_cost); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d\n", curr_score.alpha_cost); } };
  for (size_t i = 0; i < N_day; i++) {
    if (i != 0) {
      { if (fp != outlog_fp) { fprintf(fp, " "); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, " "); } };
    }
    { if (fp != outlog_fp) { fprintf(fp, "%d", curr_score.w_days[i]); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d", curr_score.w_days[i]); } };
  }
  { if (fp != outlog_fp) { fprintf(fp, "\n"); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "\n"); } };
  { if (fp != outlog_fp) { fprintf(fp, "%f %f %f %f %f\n", curr_score.w_trans, curr_score.w_ele, curr_score.w_env, curr_score.w_acc, curr_score.w_work); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%f %f %f %f %f\n", curr_score.w_trans, curr_score.w_ele, curr_score.w_env, curr_score.w_acc, curr_score.w_work); } }
                                      ;
  { if (fp != outlog_fp) { fprintf(fp, "%f %f %f %f\n", curr_score.alpha_trans_fee, curr_score.alpha_trans_penalty, curr_score.alpha_trans_canceled, curr_score.alpha_trans_undelivered); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%f %f %f %f\n", curr_score.alpha_trans_fee, curr_score.alpha_trans_penalty, curr_score.alpha_trans_canceled, curr_score.alpha_trans_undelivered); } }
                                                       ;
  { if (fp != outlog_fp) { fprintf(fp, "%f %f %f\n", curr_score.alpha_ele, curr_score.alpha_ele_FE, curr_score.alpha_ele_buy); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%f %f %f\n", curr_score.alpha_ele, curr_score.alpha_ele_FE, curr_score.alpha_ele_buy); } }
                                                                      ;
  { if (fp != outlog_fp) { fprintf(fp, "%f %f\n", curr_score.alpha_env_fuel, curr_score.alpha_env_buy); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%f %f\n", curr_score.alpha_env_fuel, curr_score.alpha_env_buy); } }
                                             ;
  { if (fp != outlog_fp) { fprintf(fp, "%d\n", curr_score.alpha_acc); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d\n", curr_score.alpha_acc); } };
  { if (fp != outlog_fp) { fprintf(fp, "%d\n", curr_score.alpha_work); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d\n", curr_score.alpha_work); } };
  return ret;
}
void judge::getGraphData(FILE *) {
  readLineSkipComment();
  do { if (!(s.size() == 2)) exit(1); } while (0);
  N = std::stoi(s[0]);
  M = std::stoi(s[1]);
  ;
  if (false) fprintf(
  stderr, "###Debug %s(%d): %zu vertices and %zu edges will be loaded.\n",
  "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp", 1001, N, M);
  v.resize(N);
  v_p.resize(N);
  for (size_t i = 0; i < N; i++) {
    readLineSkipComment();
    do { if (!(s.size() == 5)) exit(1); } while (0);
    v[i].x = std::stoi(s[0]);
    v[i].y = std::stoi(s[1]);
    v[i].p = std::stoi(s[2]);
    v[i].A = std::stoi(s[3]);
    v[i].l = std::stoi(s[4]);
    v_p[i] = v[i].p;
  }
  g = graph<edge>(N);
  u_output = std::vector<size_t>(M);
  v_output = std::vector<size_t>(M);
  c_output = std::vector<size_t>(M);
  for (size_t i = 0; i < M; i++) {
    readLineSkipComment();
    do { if (!(s.size() == 3)) exit(1); } while (0);
    size_t u = std::stoi(s[0]);
    size_t v = std::stoi(s[1]);
    size_t c = std::stoi(s[2]);
    u_output[i] = u;
    v_output[i] = v;
    c_output[i] = c;
    --u, --v;
    g.add_edge(u, v, c);
    g.add_edge(v, u, c);
  }
  g.sort_edges();
}
std::string judge::setGraphData(FILE *fp) {
  std::string ret = "OK";
  { if (fp != outlog_fp) { fprintf(fp, "%zu %zu\n", V, E); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu %zu\n", V, E); } };
  for (size_t i = 0; i < V; i++) {
    { if (fp != outlog_fp) { fprintf(fp, "%d %d %d %d %d\n", v[i].x, v[i].y, v[i].p, v[i].A, v[i].l); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d %d %d %d\n", v[i].x, v[i].y, v[i].p, v[i].A, v[i].l); } }
                             ;
  }
  for (size_t i = 0; i < E; i++) {
    { if (fp != outlog_fp) { fprintf(fp, "%zu %zu %zu\n", u_output[i], v_output[i], c_output[i]); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu %zu %zu\n", u_output[i], v_output[i], c_output[i]); } }
                                  ;
  }
  return ret;
}
void judge::getDemandData(FILE *) {
  readLineSkipComment();
  N_demand = std::stoi(s[0]);
  N_nano = N_pattern = N_demand;
  if (false) fprintf(stderr, "###Debug %s(%d), N_demand=%zu\n", "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp",
                      1076, N_demand);
  demand = Demand(N_day, N_demand, N_div);
  size_t i, j, k;
  for (i = 0; i < N_day; i++) {
    for (j = 0; j < N_demand; j++) {
      Demand_Info &demand_info = demand.day_list[i][j];
      readLineSkipComment();
      demand_info.x = std::stoi(s[0]) - 1;
      demand_info.sigma_D2 = std::stoi(s[1]);
      do { if (!(demand_info.x < V)) exit(1); } while (0);
      readLineSkipComment();
      do { if (!(s.size() == N_div)) exit(1); } while (0);
      for (k = 0; k < N_div; k++) {
        demand_info.D_predict_list[k] = std::stoi(s[k]);
      }
    }
  }
}
std::string judge::setDemandData(FILE *fp, int day, int id) {
  std::string ret = "OK";
  if (day == -1) {
    { if (fp != outlog_fp) { fprintf(fp, "%zu\n", N_demand); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu\n", N_demand); } };
  } else {
    const Demand_Info &demand_info =
    demand.day_list[day][id];
    { if (fp != outlog_fp) { fprintf(fp, "%d %d\n", demand_info.x + 1, demand_info.sigma_D2); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d\n", demand_info.x + 1, demand_info.sigma_D2); } };
    size_t k;
    for (k = 0; k < N_div; k++) {
      if (k != 0) {
        { if (fp != outlog_fp) { fprintf(fp, " "); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, " "); } };
      }
      { if (fp != outlog_fp) { fprintf(fp, "%d", demand_info.D_predict_list[k]); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d", demand_info.D_predict_list[k]); } };
    }
    { if (fp != outlog_fp) { fprintf(fp, "\n"); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "\n"); } };
  }
  return ret;
}
bool judge::readLineSkipComment() {
  bool sts = true;
  do {
    this->StrLine = getLine(stdin);
    if (outlog_fp) {
      fprintf(outlog_fp, "<< ");
      fwrite(StrLine.c_str(), 1, StrLine.length(), outlog_fp);
      fprintf(outlog_fp, "\n");
    }
    if (this->StrLine.length() > 0) {
      StringHelper::SplitToken(this->StrLine, " ", s);
    } else {
      this->StrLine = "";
      s.clear();
      sts = false;
      break;
    }
  } while (s[0][0] == '#');
  return sts;
}
void judge::getAssetData(FILE *) {
  size_t n, i;
  readLineSkipComment();
  n = std::stoi(s[0]);
  Asset.init_PV(n);
  for (i = 0; i < n; i++) {
    readLineSkipComment();
    Asset.PV_list[i].A_PV = std::stoi(s[0]);
    Asset.PV_list[i].C_PV_init = std::stoi(s[1]);
  }
  readLineSkipComment();
  n = std::stoi(s[0]);
  Asset.init_FE(n);
  for (i = 0; i < n; i++) {
    readLineSkipComment();
    Asset.FE_list[i].P_FE_min = std::stoi(s[0]);
    Asset.FE_list[i].P_FE_max = std::stoi(s[1]);
    Asset.FE_list[i].Eta_FE_min = std::stoi(s[2]);
    Asset.FE_list[i].Eta_FE_max = std::stoi(s[3]);
    Asset.FE_list[i].C_FE_init = std::stoi(s[4]);
    Asset.FE_list[i].C_FE_fuel = std::stoi(s[5]);
  }
  readLineSkipComment();
  n = std::stoi(s[0]);
  Asset.init_RB(n);
  for (i = 0; i < n; i++) {
    readLineSkipComment();
    Asset.RB_list[i].P_RB_charge = std::stoi(s[0]);
    Asset.RB_list[i].P_RB_discharge = std::stoi(s[1]);
    Asset.RB_list[i].Eta_RB = std::stoi(s[2]);
    Asset.RB_list[i].Cap_RB = std::stoi(s[3]);
    Asset.RB_list[i].C_RB_init = std::stoi(s[4]);
  }
  readLineSkipComment();
  n = std::stoi(s[0]);
  Asset.init_EVC(n);
  for (i = 0; i < n; i++) {
    readLineSkipComment();
    Asset.EVC_list[i].P_EVC_in = std::stoi(s[0]);
    Asset.EVC_list[i].P_EVC_out = std::stoi(s[1]);
    Asset.EVC_list[i].C_EVC_init = std::stoi(s[2]);
  }
  readLineSkipComment();
  n = std::stoi(s[0]);
  Asset.init_V(n);
  for (i = 0; i < n; i++) {
    readLineSkipComment();
    Asset.V_list[i].Cap_V_ele = std::stoi(s[0]);
    Asset.V_list[i].Cap_V_pop = std::stoi(s[1]);
    readLineSkipComment();
    Asset.V_list[i].P_V_charge = std::stoi(s[0]);
    Asset.V_list[i].P_V_discharge = std::stoi(s[1]);
    Asset.V_list[i].C_V_init = std::stoi(s[2]);
    Asset.V_list[i].Delta_V_move = std::stoi(s[3]);
  }
}
std::string judge::setAssetData(FILE *fp, const std::string &arg2, int idx) {
  if (false) fprintf(stderr, "###Debug >>>setAssetData(%s,%d)\n", arg2.c_str(),
                      idx);
  std::string ret = "OK";
  if (arg2 == "") {
    { if (fp != outlog_fp) { fprintf(fp, "%zu\n%zu\n%zu\n%zu\n%zu\n", Asset.N_PV, Asset.N_FE, Asset.N_RB, Asset.N_EVC, Asset.N_V); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu\n%zu\n%zu\n%zu\n%zu\n", Asset.N_PV, Asset.N_FE, Asset.N_RB, Asset.N_EVC, Asset.N_V); } }
                                                         ;
  } else if (arg2 == TEXT_PV) {
    setAssetPV(fp, idx);
  } else if (arg2 == TEXT_FE) {
    setAssetFE(fp, idx);
  } else if (arg2 == TEXT_RB) {
    setAssetRB(fp, idx);
  } else if (arg2 == TEXT_EVC) {
    setAssetEVC(fp, idx);
  } else if (arg2 == TEXT_vehicle) {
    setAssetV(fp, idx);
  }
  return ret;
}
void judge::setAssetPV(FILE *fp, int idx) {
  if (idx == -1) {
    { if (fp != outlog_fp) { fprintf(fp, "%zu\n", Asset.N_PV); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu\n", Asset.N_PV); } };
  } else {
    auto &ast = Asset.PV_list[idx];
    { if (fp != outlog_fp) { fprintf(fp, "%d %d\n", ast.A_PV, ast.C_PV_init); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d\n", ast.A_PV, ast.C_PV_init); } };
  }
}
void judge::setAssetFE(FILE *fp, int idx) {
  if (idx == -1) {
    { if (fp != outlog_fp) { fprintf(fp, "%zu\n", Asset.N_FE); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu\n", Asset.N_FE); } };
  } else {
    auto &ast = Asset.FE_list[idx];
    { if (fp != outlog_fp) { fprintf(fp, "%d %d %d %d %d %d\n", ast.P_FE_min, ast.P_FE_max, ast.Eta_FE_min, ast.Eta_FE_max, ast.C_FE_init, ast.C_FE_fuel); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d %d %d %d %d\n", ast.P_FE_min, ast.P_FE_max, ast.Eta_FE_min, ast.Eta_FE_max, ast.C_FE_init, ast.C_FE_fuel); } }
                                    ;
  }
}
void judge::setAssetRB(FILE *fp, int idx) {
  if (idx == -1) {
    { if (fp != outlog_fp) { fprintf(fp, "%zu\n", Asset.N_RB); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu\n", Asset.N_RB); } };
  } else {
    auto &ast = Asset.RB_list[idx];
    { if (fp != outlog_fp) { fprintf(fp, "%d %d %d %d %d\n", ast.P_RB_charge, ast.P_RB_discharge, ast.Eta_RB, ast.Cap_RB, ast.C_RB_init); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d %d %d %d\n", ast.P_RB_charge, ast.P_RB_discharge, ast.Eta_RB, ast.Cap_RB, ast.C_RB_init); } }
                                    ;
  }
}
void judge::setAssetEVC(FILE *fp, int idx) {
  if (idx == -1) {
    { if (fp != outlog_fp) { fprintf(fp, "%zu\n", Asset.N_EVC); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu\n", Asset.N_EVC); } };
  } else {
    auto &ast = Asset.EVC_list[idx];
    { if (fp != outlog_fp) { fprintf(fp, "%d %d %d\n", ast.P_EVC_in, ast.P_EVC_out, ast.C_EVC_init); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d %d\n", ast.P_EVC_in, ast.P_EVC_out, ast.C_EVC_init); } }
                                     ;
  }
}
void judge::setAssetV(FILE *fp, int idx) {
  if (idx == -1) {
    { if (fp != outlog_fp) { fprintf(fp, "%zu\n", Asset.N_V); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu\n", Asset.N_V); } };
  } else {
    auto &ast = Asset.V_list[idx];
    { if (fp != outlog_fp) { fprintf(fp, "%d %d\n", ast.Cap_V_ele, ast.Cap_V_pop); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d\n", ast.Cap_V_ele, ast.Cap_V_pop); } };
    { if (fp != outlog_fp) { fprintf(fp, "%d %d %d %d\n", ast.P_V_charge, ast.P_V_discharge, ast.C_V_init, ast.Delta_V_move); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d %d %d\n", ast.P_V_charge, ast.P_V_discharge, ast.C_V_init, ast.Delta_V_move); } }
                                                     ;
  }
}
void judge::getInOrderData(FILE *) {
  size_t i, j;
  in_orders.resize(N_day);
  for (i = 0; i < N_day; i++) {
    std::vector<int> &in_order_i = in_orders[i].in_order_1_ndiv;
    in_order_i.resize(N_div);
    readLineSkipComment();
    do { if (!(s.size() == N_div)) exit(1); } while (0);
    for (j = 0; j < N_div; j++) {
      in_order_i[j] = std::stoi(s[j]);
    }
  }
}
std::string judge::setInOrderData(FILE *fp, int day) {
  std::string ret = "OK";
  if (day == -1) {
    size_t i, j;
    for (i = 0; i < N_day; i++) {
      std::vector<int> &in_order_i = in_orders[i].in_order_1_ndiv;
      for (j = 0; j < N_div; j++) {
        if (j != 0) {
          { if (fp != outlog_fp) { fprintf(fp, " "); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, " "); } };
        }
        { if (fp != outlog_fp) { fprintf(fp, "%d", in_order_i[j]); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d", in_order_i[j]); } };
      }
      { if (fp != outlog_fp) { fprintf(fp, "\n"); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "\n"); } };
    }
  } else if ((size_t)day < N_day) {
    std::vector<int> &in_order_i = in_orders[day].in_order_1_ndiv;
    for (size_t i = 0; i < N_div; i++) {
      if (i != 0) {
        { if (fp != outlog_fp) { fprintf(fp, " "); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, " "); } };
      }
      { if (fp != outlog_fp) { fprintf(fp, "%d", in_order_i[i]); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d", in_order_i[i]); } };
    }
    { if (fp != outlog_fp) { fprintf(fp, "\n"); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "\n"); } };
  } else {
    { if (fp != outlog_fp) { fprintf(fp, "\n"); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "\n"); } };
  }
  return ret;
}
void judge::getWorkData(FILE *) {
  readLineSkipComment();
  work.N_work = std::stoi(s[0]);
  for (size_t i = 0; i < N_day; i++) {
    work.demands.push_back(std::vector<WorkDetail>());
    for (size_t j = 0; j < work.N_work; j++) {
      work.demands[i].push_back(WorkDetail());
      auto &w = work.demands[i][j];
      readLineSkipComment();
      w.x = std::stoi(s[0]) - 1;
      w.delta_work = std::stoi(s[1]);
      w.I_work_min = std::stoi(s[2]);
      w.D_work = std::stoi(s[3]);
      assert(w.x < N);
      readLineSkipComment();
      w.Cap_work_ele = std::stoi(s[0]);
      w.V_work_charge = std::stoi(s[1]);
      w.V_work_discharge = std::stoi(s[2]);
      w.Eta_work = std::stoi(s[3]);
      readLineSkipComment();
      for (size_t k = 0; k < N_div; k++) {
        w.A_work.push_back(std::stoi(s[k]));
      }
    }
  }
}
std::string judge::setWorkData(FILE *fp, int day, int id) {
  ;
  std::string ret = "OK";
  if (day < 0) {
    { if (fp != outlog_fp) { fprintf(fp, "%zu\n", work.N_work); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu\n", work.N_work); } };
  } else {
    assert(N_day == work.demands.size());
    assert(work.N_work == work.demands[day].size());
    auto &w = work.demands[day][id];
    { if (fp != outlog_fp) { fprintf(fp, "%d %d %d %d\n", w.x + 1, w.delta_work, w.I_work_min, w.D_work); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d %d %d\n", w.x + 1, w.delta_work, w.I_work_min, w.D_work); } }
                               ;
    { if (fp != outlog_fp) { fprintf(fp, "%d %d %d %d\n", w.Cap_work_ele, w.V_work_charge, w.V_work_discharge, w.Eta_work); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d %d %d\n", w.Cap_work_ele, w.V_work_charge, w.V_work_discharge, w.Eta_work); } }
                                                     ;
    assert(N_div == w.A_work.size());
    for (size_t i = 0; i < N_div; i++) {
      if (i != 0) {
        { if (fp != outlog_fp) { fprintf(fp, " "); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, " "); } };
      }
      { if (fp != outlog_fp) { fprintf(fp, "%d", w.A_work[i]); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d", w.A_work[i]); } };
    }
    { if (fp != outlog_fp) { fprintf(fp, "\n"); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "\n"); } };
  }
  return ret;
}
void judge::getShelterData(FILE *) {
  size_t n_shelter;
  readLineSkipComment();
  n_shelter = std::stoi(s[0]);
  shlt.init(n_shelter, N_div);
  for (size_t i = 0; i < n_shelter; i++) {
    ;
    readLineSkipComment();
    shlt.shelter_data[i].x = std::stoi(s[0]) - 1;
    shlt.shelter_data[i].p = std::stoi(s[1]);
    assert(shlt.shelter_data[i].x < N);
  }
  if (false) fprintf(stderr, "###Debug %s(%d), N_div=%zu\n", "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp",
                      1451, N_div);
  readLineSkipComment();
  for (size_t i = 0; i < s.size(); i++) {
    shlt.shelter_D[i] = std::stoi(s[i]);
  }
}
std::string judge::setShelterData(FILE *fp) {
  std::string ret = "OK";
  { if (fp != outlog_fp) { fprintf(fp, "%zu\n", shlt.N_shelter); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%zu\n", shlt.N_shelter); } };
  size_t i;
  for (i = 0; i < shlt.N_shelter; i++) {
    { if (fp != outlog_fp) { fprintf(fp, "%d %d\n", shlt.shelter_data[i].x + 1, shlt.shelter_data[i].p); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d %d\n", shlt.shelter_data[i].x + 1, shlt.shelter_data[i].p); } }
                                             ;
  }
  for (i = 0; i < N_div; i++) {
    if (i != 0) {
      { if (fp != outlog_fp) { fprintf(fp, " "); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, " "); } };
    }
    { if (fp != outlog_fp) { fprintf(fp, "%d", shlt.shelter_D[i]); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%d", shlt.shelter_D[i]); } };
  }
  { if (fp != outlog_fp) { fprintf(fp, "\n"); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "\n"); } };
  return ret;
}
void judge::getRadiationData(FILE *) {
  ;
  ;
  readLineSkipComment();
  size_t n_weather = std::stoi(s[0]);
  rad.init(N_day, n_weather, N_div);
  readLineSkipComment();
  if (s.size() != n_weather) {
   
                              ;
    exit(1);
  }
  for (size_t i = 0; i < n_weather; i++) {
    rad.station_x[i] = std::stoi(s[i]) - 1;
  }
  ;
  for (size_t i = 0; i < N_day; i++) {
    for (size_t j = 0; j < n_weather; j++) {
      std::vector<double> &R = rad.weather_info_predict[i].R[j];
      readLineSkipComment();
      if (N_div != s.size()) {
        ;
        ;
        for (auto &token : s)
          ;
        exit(1);
      }
      for (size_t k = 0; k < N_div; k++) {
        R[k] = std::stof(s[k]);
      }
    }
  }
  ;
  for (size_t i = 0; i < N_day; i++) {
    for (size_t j = 0; j < n_weather; j++) {
      std::vector<double> &R = rad.weather_info_actual[i].R[j];
      readLineSkipComment();
      if (N_div != s.size()) {
        ;
        ;
        for (auto &token : s)
          ;
        exit(1);
      }
      for (size_t k = 0; k < N_div; k++) {
        R[k] = std::stof(s[k]);
      }
    }
  }
  ;
  for (size_t n = 0; n < rad.N_dummy; n++) {
    for (size_t i = 0; i < N_day; i++) {
      for (size_t j = 0; j < n_weather; j++) {
        std::vector<double> &R = rad.weather_info_dummy[n][i].R[j];
        readLineSkipComment();
        if (N_div != s.size()) {
          ;
          ;
          for (auto &token : s)
            ;
          exit(1);
        }
        for (size_t k = 0; k < N_div; k++) {
          R[k] = std::stof(s[k]);
        }
      }
    }
  }
  ;
}
std::string judge::setRadiationData(FILE *fp, int day, int id) {
  std::string ret = "OK";
  std::vector<double> R = calcRadRValue(day, id, RadiationCalcType::CT_PREDICT);
  for (size_t i = 0; i < N_div; i++) {
    if (i != 0) {
      { if (fp != outlog_fp) { fprintf(fp, " "); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, " "); } };
    }
    { if (fp != outlog_fp) { fprintf(fp, "%f", R[i]); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "%f", R[i]); } };
  }
  { if (fp != outlog_fp) { fprintf(fp, "\n"); } if (outlog_fp && fp != stderr) { fprintf(outlog_fp, "\n"); } };
  return ret;
}
std::vector<double> judge::calcRadRValue(int day,
                                         int vertex_idx,
                                         const RadiationCalcType &calcType) {
  if (false) fprintf(stderr, "###Debug >>>calcRadRValue(%d,%d,%d)\n", day,
                      vertex_idx, calcType);
  std::vector<double> retR(rad.N_div);
  do { if (!((size_t)vertex_idx < v.size())) exit(1); } while (0);
  weather_info weather;
  if (calcType == RadiationCalcType::CT_PREDICT) {
    weather = rad.weather_info_predict[day];
  } else if (calcType == RadiationCalcType::CT_ACTUAL) {
    weather = rad.weather_info_actual[day];
  } else if (calcType == RadiationCalcType::CT_DUMMY) {
    int dummy_index = random_helper.nextInt(rad.N_dummy);
    weather = rad.weather_info_dummy[dummy_index][day];
  }
  std::vector<double> d(rad.N_weather);
  for (size_t i = 0; i < rad.N_weather; i++) {
    d[i] = distance2D(v[vertex_idx].x, v[vertex_idx].y, v[rad.station_x[i]].x,
                      v[rad.station_x[i]].y);
    if (false) fprintf(
    stderr, "### Debug calcRadRValue: Dist=%f, x1=%d,y1=%d, x2=%d,y2=%d\n",
    d[i], v[vertex_idx].x, v[vertex_idx].y, v[rad.station_x[i]].x,
    v[rad.station_x[i]].y);
  }
  std::vector<double> d_mul(rad.N_weather);
  for (size_t n = 0; n < rad.N_div; n++) {
    double numerator = 0.0, denominator = 1.0;
    for (size_t i = 0; i < rad.N_weather; i++) {
      d_mul[i] = 1.0;
      if (false) fprintf(stderr, "### Debug calcRadRValue: R: %f\n",
                          weather.R[i][n]);
      for (size_t j = 0; j < rad.N_weather; j++) {
        if (i != j) {
          weather.R[i][n] *= d[j];
          d_mul[i] *= d[j];
        }
      }
    }
    for (size_t i = 0; i < rad.N_weather; ++i)
      numerator += weather.R[i][n];
    denominator =
    std::accumulate(d_mul.begin(), d_mul.end(),
                    0.0);
    retR[n] = numerator / denominator;
  }
  return retR;
}
int judge::sample_vertex(const std::vector<int> &selection_table,
                         int normalizing_constant,
                         std::mt19937_64 &engine) {
  const int selection =
  std::uniform_int_distribution<int>(1, normalizing_constant)(engine);
  int left = 0, right = selection_table.size();
  while (right - left > 1) {
    const int center = (right + left) / 2;
    do { if (!((size_t)center < selection_table.size())) exit(1); } while (0);
    if (selection <= selection_table[center])
      right = center;
    else if (selection > selection_table[center])
      left = center;
  }
  return left;
}
void judge::create_orders(const std::vector<int> &o,
                          const std::vector<int> &p,
                          std::mt19937_64 &engine,
                          std::vector<OrderB> &todayOrders) {
  const int V = p.size();
  ;
  std::vector<int> selection_table(V + 1, 0);
  int normalizing_constant = 0;
  for (int v = 1; v <= V; ++v) {
    selection_table[v] = p[v - 1] + selection_table[v - 1];
    normalizing_constant += p[v - 1];
  }
  ;
  for (size_t i = 0; i < o.size(); ++i) {
    const int start = i * (T_max / o.size()) + 1;
    const int end = (i + 1) * (T_max / o.size());
    const int N = std::poisson_distribution<int>(o[i])(engine);
    if (false) { fprintf(stderr, "create_orders: N=%d\n", N); }
    for (int n = 0; n < N; ++n) {
      int w = sample_vertex(selection_table, normalizing_constant, engine),
          z = sample_vertex(selection_table, normalizing_constant, engine);
      while (w == z)
        z = sample_vertex(selection_table, normalizing_constant, engine);
      int time = std::uniform_int_distribution<int>(start, end)(engine);
      if (time <= (int)T_last) {
        do { if (!(time > 0)) exit(1); } while (0);
        todayOrders.emplace_back(OrderB(w, z, time));
      }
    }
  }
  std::sort(
  todayOrders.begin(), todayOrders.end(),
  [](const auto &o1, const auto &o2) { return o1.startTime < o2.startTime; });
  for (size_t i = 0; i < todayOrders.size(); i++) {
    todayOrders[i].id = i;
  }
}
void judge::createOrders(size_t day, bool ignore_order) {
  if (false) fprintf(stderr,
                      "###Debug >>>createOrders(day=%zu,ignore_order=%d)\n",
                      day, ignore_order);
  ;
  ;
  int rnd = random_helper.nextInt();
  std::mt19937_64 engine(static_cast<unsigned int>(rnd));
  std::vector<OrderB> todayOrders;
  if (!ignore_order) {
    create_orders(in_orders[day].in_order_1_ndiv, v_p, engine, todayOrders);
  }
  this->p_trans_const = todayOrders.size() / this->T_last;
  if (false) fprintf(stderr, "###Debug　3-13 N_order=%zu\n",
                      todayOrders.size());
  allOrders.clear();
  allOrders.resize(T_max + 1);
  for (auto &o : todayOrders) {
    allOrders[o.startTime].emplace_back(o);
  }
  activeOrders.clear();
}
std::string judge::set_Algorithm_Initial_Input1(const bool submitFlag,
                                                const size_t day,
                                                std::vector<std::string> &,
                                                Main &main,
                                                StatusOnAcc *acc_stat) {
  ;
  if (false) fprintf(
  stderr,
  "###Debug "
  ">>>set_Algorithm_Initial_Input1(submitFlag=%d,day=%zu)\n",
  submitFlag, day);
  std::string result = "OK";
  RadiationCalcType radtype;
  if (submitFlag) {
    radtype = RadiationCalcType::CT_ACTUAL;
  } else {
    radtype = RadiationCalcType::CT_DUMMY;
  }
  if (false) fprintf(stderr, "###Debug %s(%d): before fprintf: N_sol=%zu\n",
                      "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp", 1807, N_sol);
  main.A_Data.numSol = N_sol;
  if (false) fprintf(stderr, "###Debug %s(%d): before fprintf: N=%zu,M=%zu\n",
                      "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp", 1811, N, M);
  main.A_Data.numVertexes = N;
  main.A_Data.numEdges = M;
  {
  }
  if (false) fprintf(stderr,
                      "###Debug Daytype=%zu,N_pattern=%zu,dumping u v d...\n",
                      Daytype, N_pattern);
  do { if ((M) != ((size_t)main.A_Data.numEdges)) { ; ; ; exit(1); } } while (0);
  ;
  do { if ((M) != (u_output.size())) { ; ; ; exit(1); } } while (0);
  do { if ((M) != (v_output.size())) { ; ; ; exit(1); } } while (0);
  do { if ((M) != (c_output.size())) { ; ; ; exit(1); } } while (0);
  main.A_Data.edges.resize(main.A_Data.numVertexes);
  for (size_t i = 0; i < M; i++) {
    size_t v1 = u_output[i], v2 = v_output[i], d = c_output[i];
    --v1, --v2;
    do { if (!((int)v1 < main.A_Data.numVertexes)) exit(1); } while (0);
    do { if (!((int)v2 < main.A_Data.numVertexes)) exit(1); } while (0);
    main.A_Data.edges[v1].emplace_back(v2, d);
    main.A_Data.edges[v2].emplace_back(v1, d);
  }
  for (auto &edge : main.A_Data.edges)
    edge.shrink_to_fit();
  ;
  main.A_Data.dayType = Daytype;
  main.A_Data.numDivs = N_div;
  main.A_Data.numPatterns = N_pattern;
  main.A_Data.varEle = sigma_ele;
  main.A_Data.pEvent = p_event;
  main.A_Data.deltaEvent = Delta_event;
  if (false) fprintf(
  stderr, "###Debug 3-5,Ndiv=%d,Npattern=%d,sigma_ele=%d,Pevent=%d,Devent=%d\n",
  main.A_Data.numDivs, main.A_Data.numPatterns, main.A_Data.varEle,
  main.A_Data.pEvent, main.A_Data.deltaEvent);
  main.A_Data.tMax = T_max;
  main.A_Data.tDiv = main.A_Data.tMax / main.A_Data.numDivs;
  ;
  ;
  main.A_Data.grids.clear();
  main.A_Data.grids.resize(demand.N_demand);
  pw.resize(demand.N_demand);
  for (size_t n = 0; n < demand.N_demand; ++n) {
    Grid *grid_data = new Grid();
    pw[n].resize(N_div);
    main.A_Data.declaredGrid.push_back(grid_data);
    main.A_Data.grids[n] = grid_data;
    grid_data->grid_id = n;
    grid_data->is_nano = false;
    grid_data->vertex = demand.day_list[day][n].x;
    grid_data->predictedEnergyBalanceBase.resize(main.A_Data.tMax);
    grid_data->predictedEnergyBalanceWithOrders.resize(main.A_Data.tMax);
    for (size_t t = 0; t < (size_t)main.A_Data.tMax; ++t) {
      grid_data->predictedEnergyBalanceBase[t] =
      grid_data->predictedEnergyBalanceWithOrders[t] =
      -demand.day_list[day][n].D_predict_list[t / main.A_Data.tDiv];
    }
    for (size_t t = 0; t < (size_t)main.A_Data.numDivs; ++t)
      pw[n][t] = -demand.day_list[day][n].D_predict_list[t];
  }
  ;
  for (size_t n = 0; n < Grid_Info.N_grid; ++n) {
    auto &g = Grid_Info.data_list[n];
    bool is_found = false;
    auto R = calcRadRValue(day, g.x_grid_pos, CT_PREDICT);
    auto R_actual = calcRadRValue(day, g.x_grid_pos, radtype);
    ;
    for (auto r : R)
      ;
    ;
    int demand_cnt = 0;
    for (auto *grid_data : main.A_Data.grids) {
      if (grid_data->vertex == g.x_grid_pos) {
        ;
        is_found = true;
        if (acc_stat && acc_stat->acc_mode) {
          grid_data->charge = acc_stat->grid_cap[grid_data->grid_id];
        } else {
          grid_data->charge = g.chg_grid_init;
        }
        grid_data->rb = Asset.getRBinfo(g.type_grid_RB);
        grid_data->Cap_RB_total = grid_data->rb->Cap_RB * g.A_grid_RB;
        grid_data->evc = Asset.getEVCinfo(g.type_grid_EVC);
        grid_data->fe = Asset.getFEinfo(g.type_grid_FE);
        grid_data->V_in_Max = grid_data->evc->P_EVC_in;
        grid_data->V_out_Max = grid_data->evc->P_EVC_out;
        grid_data->P_FE = 0;
        grid_data->is_nano = true;
        for (size_t t = 0; t < (size_t)main.A_Data.tMax; ++t) {
          grid_data->predictedEnergyBalanceBase[t] =
          grid_data->predictedEnergyBalanceWithOrders[t] =
          g.A_grid_PV * R[t / main.A_Data.tDiv] -
          demand.day_list[day][demand_cnt].D_predict_list[t / main.A_Data.tDiv];
        }
        for (size_t t = 0; t < (size_t)main.A_Data.numDivs; ++t)
          pw[demand_cnt][t] =
          g.A_grid_PV * R_actual[t] -
          demand.day_list[day][demand_cnt].D_predict_list[t];
        break;
      }
      demand_cnt++;
    }
    if (not is_found) {
      ;
      Grid *grid_data = new Grid();
      main.A_Data.declaredGrid.push_back(grid_data);
      main.A_Data.grids.emplace_back(grid_data);
      grid_data->grid_id = main.A_Data.grids.size() - 1;
      grid_data->is_nano = true;
      grid_data->vertex = g.x_grid_pos;
      if (acc_stat && acc_stat->acc_mode) {
        grid_data->charge = acc_stat->grid_cap[grid_data->grid_id];
      } else {
        grid_data->charge = g.chg_grid_init;
      }
      grid_data->predictedEnergyBalanceBase.resize(main.A_Data.tMax);
      grid_data->predictedEnergyBalanceWithOrders.resize(main.A_Data.tMax);
      grid_data->rb = Asset.getRBinfo(g.type_grid_RB);
      grid_data->evc = Asset.getEVCinfo(g.type_grid_EVC);
      grid_data->fe = Asset.getFEinfo(g.type_grid_FE);
      grid_data->V_in_Max = grid_data->evc->P_EVC_in;
      grid_data->V_out_Max = grid_data->evc->P_EVC_out;
      grid_data->Cap_RB_total = grid_data->rb->Cap_RB * g.A_grid_RB;
      grid_data->P_FE = 0;
      for (size_t t = 0; t < (size_t)main.A_Data.tMax; ++t) {
        grid_data->predictedEnergyBalanceBase[t] =
        grid_data->predictedEnergyBalanceWithOrders[t] =
        g.A_grid_PV * R[t / main.A_Data.tDiv];
      }
      pw.resize(pw.size() + 1);
      pw.back().resize(N_div);
      for (size_t t = 0; t < (size_t)main.A_Data.numDivs; ++t)
        pw.back()[t] = g.A_grid_PV * R_actual[t];
    }
  }
  if (false) {
    size_t grid_cnt = 0;
    for ([[maybe_unused]] auto const &g : main.A_Data.grids) {
      fprintf(stderr, "BEGIN pattern %zu:\n", grid_cnt);
      for (const auto &p :
           main.A_Data.grids[grid_cnt]->predictedEnergyBalanceBase) {
        fprintf(stderr, "%d ", p);
      }
      fprintf(stderr, "END pattern %zu:\n", grid_cnt++);
    }
  }
  main.A_Data.vertexToGrid =
  std::vector<Grid *>(main.A_Data.numVertexes, nullptr);
  for (auto &g : main.A_Data.grids) {
    do { if (!((size_t)g->vertex < main.A_Data.vertexToGrid.size())) exit(1); } while (0);
    main.A_Data.vertexToGrid[g->vertex] = g;
  }
  for (size_t i = 0; i < this->g.nodes.size(); i++) {
    this->g.nodes[i].type = 0;
    this->g.nodes[i].cap = 0;
    this->g.nodes[i].max_cap = 0;
    this->g.nodes[i].node_id = i;
    this->g.nodes[i].grid_id = -1;
  }
  for (size_t i = 0; i < main.A_Data.grids.size(); i++) {
    this->g.nodes[main.A_Data.grids[i]->vertex].grid_id = i;
  }
  for (size_t i = 0; i < main.A_Data.grids.size(); i++) {
    size_t ix = main.A_Data.grids[i]->vertex;
    do { if (!(ix < this->g.nodes.size())) exit(1); } while (0);
    this->g.nodes[ix].type = 1;
    this->g.nodes[ix].cap = main.A_Data.grids[i]->charge;
    this->g.nodes[ix].max_cap = main.A_Data.grids[i]->Cap_RB_total;
  }
  if (false) {
    fprintf(stderr, "### Debug N_grid=%zu\n", Grid_Info.N_grid);
    for (auto g : Grid_Info.data_list) {
      g.dump(stderr);
    }
  }
  N_pattern = N_nano = main.A_Data.grids.size();
  if (false) fprintf(stderr,
                      "###Debug %s(%d), N_nano = %zu, Grid_Info.N_grid = %zu\n",
                      "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp", 2112, N_nano, Grid_Info.N_grid);
  if (false) {
    fprintf(stderr, "###Debug N_EV=%zu\n", ev_info.N_EV);
    ev_info.dump(stderr);
  }
  main.A_Data.numGrids = N_nano;
  ;
  main.A_Data.numVehicles = ev_info.N_EV;
  main.A_Data.vehicles = std::vector<Vehicle *>(main.A_Data.numVehicles);
  ;
  for (size_t i = 0; i < (size_t)main.A_Data.numVehicles; i++) {
    do { if (!(i < ev_info.data_list.size())) exit(1); } while (0);
    auto &ev_data = ev_info.data_list[i];
    if (acc_stat && acc_stat->acc_mode) {
      position &pos = acc_stat->vehicle_pos[i];
      if (pos.from == pos.to) {
        main.A_Data.vehicles[i] = new Vehicle(pos.from);
      } else {
        main.A_Data.vehicles[i] = new Vehicle(pos.from, pos.to, pos.distance,
                                              pos.edge_distance - pos.distance);
      }
      main.A_Data.vehicles[i]->C_e_init = acc_stat->vehicle_cap[i];
    } else {
      main.A_Data.vehicles[i] = new Vehicle(ev_data.x_EV_pos);
      main.A_Data.vehicles[i]->C_e_init = ev_data.Chg_EV_init;
    }
    assert((size_t)ev_data.type_EV < Asset.V_list.size());
    main.A_Data.vehicles[i]->C_e_max = Asset.V_list[ev_data.type_EV].Cap_V_ele;
    main.A_Data.vehicles[i]->V_in_max =
    Asset.V_list[ev_data.type_EV].P_V_charge;
    main.A_Data.vehicles[i]->V_out_max =
    Asset.V_list[ev_data.type_EV].P_V_discharge;
    main.A_Data.vehicles[i]->N_max = Asset.V_list[ev_data.type_EV].Cap_V_pop;
    main.A_Data.vehicles[i]->Delta_move =
    Asset.V_list[ev_data.type_EV].Delta_V_move;
    main.A_Data.vehicles[i]->charge = main.A_Data.vehicles[i]->C_e_init;
    if (false) {
      fprintf(
      stderr,
      "3-7-2-6-5 part1 pos=%d C_e_init=%d C_e_max=%d V_max=%d N_max=%d "
      "Delta_move=%d\n",
      main.A_Data.vehicles[i]->vertex0, main.A_Data.vehicles[i]->C_e_init,
      main.A_Data.vehicles[i]->C_e_max, main.A_Data.vehicles[i]->V_in_max,
      main.A_Data.vehicles[i]->N_max, main.A_Data.vehicles[i]->Delta_move);
    }
  }
  ;
  vehicles.resize(ev_info.N_EV);
  for (size_t i = 0; i < vehicles.size(); ++i) {
    vehicles[i].max_cap = main.A_Data.vehicles[i]->C_e_max;
    vehicles[i].cap = main.A_Data.vehicles[i]->C_e_init;
    if (acc_stat && acc_stat->acc_mode) {
      vehicles[i].pos = acc_stat->vehicle_pos[i];
    } else {
      vehicles[i].pos = position(ev_info.data_list[i].x_EV_pos,
                                 ev_info.data_list[i].x_EV_pos, 0, 0);
    }
    vehicles[i].delta_move = main.A_Data.vehicles[i]->Delta_move;
    vehicles[i].V_in_Max_EV = main.A_Data.vehicles[i]->V_in_max;
    vehicles[i].V_out_Max_EV = main.A_Data.vehicles[i]->V_out_max;
    vehicles[i].N_Max_Trans = main.A_Data.vehicles[i]->N_max;
    if (false) {
      fprintf(stderr, "3-7-2-6-5 part2 pos=(%zu %zu %zu %zu)\n",
              vehicles[i].pos.from, vehicles[i].pos.to,
              vehicles[i].pos.distance, vehicles[i].pos.edge_distance);
    }
  }
  ;
  main.A_Data.penaltyOrder = P_trans;
  main.A_Data.penaltyOutsideSupply = static_cast<int>(std::round(Gamma));
  main.A_Data.tMax = T_max;
  main.A_Data.tDiv = main.A_Data.tMax / main.A_Data.numDivs;
  if (false) fprintf(stderr, "###Debug 3-8 P_trans=%d,T_max=%d\n",
                      main.A_Data.penaltyOrder, main.A_Data.tMax);
  if (false) fprintf(
  stderr, "###Debug <<<set_Algorithm_Initial_Input1(submitFlag=%d,day=%zu)\n",
  submitFlag, day);
  work.status.clear();
  for (size_t i = 0; i < work.N_work; i++) {
    work.status.push_back(WorkStatus(i, &work.demands[day][i]));
    if (acc_stat && acc_stat->acc_mode) {
      work.status[i].charge = acc_stat->work_cap[i];
    }
  }
  return result;
}
int judge::set_Algorithm_Initial_Input2(const bool submitFlag,
                                        Main &main,
                                        const size_t day,
                                        bool ignore_order) {
  if (false) fprintf(
  stderr, "###Debug >>>set_Algorithm_Initial_Input2(submitFlag=%d,day=%zu)\n",
  submitFlag, day);
  int retVal = 0;
  createOrders(day, ignore_order);
  if (submitFlag) {
    int rnd = random_helper.nextInt();
    if (false) fprintf(stderr,
                        "### 4-2: set_Algorithm_Initial_Input2 rnd=%d\n", rnd);
    setPWerrorGenSeed(static_cast<unsigned int>(rnd));
  }
  createNanoGrid(day);
  if (false) fprintf(
  stderr, "###Debug <<<set_Algorithm_Initial_Input2(submitFlag=%d,day=%zu)\n",
  submitFlag, day);
  return retVal;
}
void judge::output3(const Main &main, std::ostream &dest, bool comment) {
  ;
  ;
  if (comment) {
    dest << "# turn: " << T_now << "\n";
    dest << "# Chg_grid pw_actual pw_excess pw_FE, pw_buy\n";
  }
  for (size_t i = 0; i < main.A_Data.grids.size(); ++i) {
    Grid *g = main.A_Data.grids[i];
    if (g->is_nano) {
      dest << g->charge << " " << g->prevActual << " " << g->prevExcess << " "
           << g->prevFE << " " << g->prevLbuy << std::endl;
    }
  }
  dest << std::flush;
  if (comment) {
    dest << "# Chg_EV u v dist N_order o ...\n";
  }
  for (size_t i = 0; i < main.A_Data.vehicles.size(); ++i) {
    auto &v = main.A_Data.vehicles[i];
    dest << v->charge << " " << (v->vertex1 + 1) << " " << (v->vertex2 + 1)
         << " " << v->dist1 << " " << v->carryingOrderIds.size();
    for (auto &o : v->carryingOrderIds) {
      dest << " " << (o + 1);
    }
    dest << std::endl;
  }
  dest << std::flush;
  if (comment) {
    dest << "# Chg_work x W w\n";
  }
  ;
  for (auto &w : work.status) {
    int wt = 0;
    if (w.startTime >= 0) {
      wt = T_now - w.startTime;
    }
   
                                       ;
    dest << w.charge << " " << (w.detail->x + 1) << " " << w.yield << " " << wt
         << std::endl;
  }
  dest << std::flush;
  std::vector<OrderB *> sendOrders;
  for (auto &o : activeOrders) {
    if (o->status == 0 || o->status == 1 ||
        o->status == 2) {
      sendOrders.push_back(o);
    } else if (o->status == -1 || o->status == -2) {
      if (!o->sendFlag) {
        sendOrders.push_back(o);
      }
    }
  }
  ;
  if (comment) {
    dest << "# N_order\n";
  }
  dest << sendOrders.size() << "\n";
  if (comment) {
    dest << "# id w z state time\n";
  }
  for (OrderB *o : sendOrders) {
    dest << (o->id + 1) << " " << (o->orig + 1) << " " << (o->dest + 1) << " "
         << o->status << " " << o->startTime << "\n";
  }
  dest << std::flush;
}
void judge::dumpForDebuggingScore(std::ofstream &ev1,
                                  std::ofstream &ev2,
                                  std::ofstream &grid1,
                                  std::ofstream &grid2,
                                  const bool,
                                  const Main &main,
                                  const size_t &,
                                  const size_t
) {
  const char EOL = '\n';
  const char SPACE = ' ';
  const AlgorithmData &A_Data = main.A_Data;
  for (int i = 0; i < A_Data.numVehicles; i++) {
    ev1 << A_Data.vehicles[i]->vertex1 << SPACE << A_Data.vehicles[i]->vertex2
        << SPACE << A_Data.vehicles[i]->charge << SPACE
        << A_Data.vehicles[i]->C_e_init << SPACE << A_Data.vehicles[i]->C_e_max
        << SPACE << A_Data.vehicles[i]->V_in_max << SPACE
        << A_Data.vehicles[i]->N_max << SPACE << A_Data.vehicles[i]->Delta_move
        << EOL;
  }
  std::set<size_t> orders;
  for (size_t i = 0; i < vehicles.size(); i++) {
    ev2 << vehicles[i].pos.from << SPACE << vehicles[i].pos.to << SPACE
        << vehicles[i].pos.distance << SPACE << vehicles[i].pos.edge_distance
        << SPACE << vehicles[i].cap << SPACE << vehicles[i].max_cap << SPACE
        << EOL;
  }
  for (size_t i = 0; i < A_Data.grids.size(); i++) {
    Grid *g = A_Data.grids[i];
    grid1 << g->charge << SPACE << g->prevActual << SPACE << g->prevExcess
          << SPACE << g->prevBuy << EOL;
  }
  for (size_t i = 0; i < this->g.nodes.size(); i++) {
    grid2 << this->g.nodes[i].node_id << SPACE << this->g.nodes[i].cap << SPACE
          << this->g.nodes[i].max_cap << SPACE << this->g.nodes[i].pw_buy
          << SPACE << A_Data.vertexToGrid[this->g.nodes[i].node_id]->P_FE
          << SPACE << this->g.nodes[i].L_buy << SPACE << EOL;
  }
}
int judge::calc_pw_error(const size_t day, const size_t id) {
  if (id >= demand.N_demand) {
    return 0;
  }
  do { if (!(day < demand.day_list.size())) exit(1); } while (0);
  do { if (!(id < demand.day_list[day].size())) exit(1); } while (0);
  Demand_Info &demand_info = demand.day_list[day][id];
  std::normal_distribution<> d{0, sqrt(demand_info.sigma_D2)};
  int delta = std::round(d(pw_error_gen));
  return delta;
}
int judge::createNanoGrid(const size_t day) {
  int retVal = 0;
  [[maybe_unused]] int pw_actual, delta = 0;
  energies =
  std::vector<std::vector<energy>>(T_max * N_sol, std::vector<energy>(N_nano));
  if (false) fprintf(
  stderr,
  "###Debug 3-12-4 N_nano=%zu, N_demand=%zu,demand.day_list[0].size=%zu\n",
  N_nano, demand.N_demand, demand.day_list[0].size());
  for (size_t i = 0; i < T_max; i++) {
    for (size_t j = 0; j < N_nano; j++) {
      do { if (!(j < pw.size())) exit(1); } while (0);
      do { if (!(i / (T_max / N_div) < pw[j].size())) exit(1); } while (0);
      do { if (!(i < energies.size())) exit(1); } while (0);
      do { if (!(j < energies[i].size())) exit(1); } while (0);
      delta = calc_pw_error(day, j);
      energies[i][j] = energy(j, pw[j][i / (T_max / N_div)] + delta);
    }
  }
  return retVal;
}
std::string judge::run_Algorithm(const bool submitFlag,
                                 Main &main,
                                 const size_t &time,
                                 const size_t day,
                                 bool onAcc) {
  ;
  if (false) fprintf(
  stderr, "###Debug >>>run_Algorithm(submitFlag=%d,time=%zu,day=%zu)\n",
  submitFlag, time, day);
  std::string result = "OK";
  if (time == 0) {
    ;
    main.init(v);
    for (size_t i = 0; i < vehicles.size(); i++)
      vehicles[i].orders.clear();
  }
  for (size_t i = 0; i < this->g.nodes.size(); i++) {
    if (this->g.nodes[i].is_grid()) {
      Grid *g = main.A_Data.vertexToGrid[i];
      g->charge = this->g.nodes[i].cap;
      g->prevActual = this->g.nodes[i].pw_actual;
      g->prevExcess = this->g.nodes[i].pw_excess;
      g->prevBuy = this->g.nodes[i].pw_buy;
      g->prevFE = this->g.nodes[i].L_FE;
      g->prevLbuy = this->g.nodes[i].L_buy;
    }
  }
  if (false) fprintf(stderr, "###Debug %s(%d),vehicles.size=%zu\n", "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp",
                      2823, vehicles.size());
  for (size_t i = 0; i < N_vehicle; i++) {
    if (false) fprintf(stderr, "###Debug %s(%d),i=%zu\n", "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp", 2827,
                        i);
    int u, v;
    size_t N_can_go, dist_u, dist_v;
    u = vehicles[i].now_vertex();
    std::vector<size_t> can_go_vertices;
    if (u == -1) {
      u = vehicles[i].pos.from;
      v = vehicles[i].pos.to;
      dist_u = vehicles[i].pos.distance;
      dist_v = vehicles[i].pos.rest_distance();
      N_can_go = 2;
      can_go_vertices.push_back(u);
      can_go_vertices.push_back(v);
    } else {
      v = u;
      dist_u = 0;
      dist_v = 0;
      N_can_go = 0;
      for (edge e : g.g[u]) {
        N_can_go++;
        can_go_vertices.push_back(e.dst);
      }
    }
    Vehicle *main_v = main.A_Data.vehicles[i];
    main_v->charge = vehicles[i].cap;
    main_v->vertex1 = u;
    main_v->vertex2 = v;
    main_v->dist1 = dist_u;
    main_v->dist2 = dist_v;
    main_v->adj = std::vector<int>(N_can_go);
    for (size_t j = 0; j < N_can_go; j++) {
      main_v->adj[j] = can_go_vertices[j];
    }
    ;
    main_v->carryingOrderIds.clear();
    for (size_t j : vehicles[i].orders) {
      main_v->carryingOrderIds.push_back((int)j);
    }
  }
  ;
  {
    std::ostringstream oss;
    output3(main, oss, false);
    std::string str3 = oss.str();
    ;
    fwrite(str3.c_str(), 1, str3.length(), stdout);
    fflush(stdout);
  }
  if (outlog_fp) {
    std::ostringstream oss;
    output3(main, oss, true);
    std::string str3 = oss.str();
    fwrite(str3.c_str(), 1, str3.length(), outlog_fp);
    fflush(outlog_fp);
  }
  {
    for (auto &o : activeOrders) {
      if (o->status == -1 || o->status == -2) {
        o->sendFlag = true;
      }
    }
  }
  ;
  {
    std::vector<Command2> commands;
    getCommands(commands);
    ;
    do_judge(main, commands, onAcc);
    ;
  }
  if (false) fprintf(
  stderr, "###Debug <<<run_Algorithm(submitFlag=%d,time=%zu,day=%zu)\n",
  submitFlag, time, day);
  return "";
}
void judge::getCommands(std::vector<Command2> &commands) {
  ;
  while (true) {
    readLineSkipComment();
    ;
    if (this->StrLine == "end") {
      break;
    }
    if (s.size() < 3) {
      ;
      exit(1);
    }
    Command2 c;
    c.group = s[0];
    c.id = std::stoi(s[1]) - 1;
    if (c.group == "FE") {
      if (s.size() != 3) {
        ;
        exit(1);
      }
      c.param1 = std::stoi(s[2]);
    } else if (c.group == "Machinery") {
      if (s.size() < 3) {
        ;
        exit(1);
      }
      c.command = s[2];
      if (c.command == "charge_from" || c.command == "charge_to") {
        if (s.size() != 4) {
          ;
          exit(1);
        }
        c.param1 = std::stoi(s[3]);
      } else if (c.command == "work" || c.command == "break") {
      } else {
        ;
        exit(1);
      }
    } else if (c.group == "Order") {
      if (s.size() != 3) {
        ;
        exit(1);
      }
      c.command = s[2];
      if (c.command == "accept" || c.command == "reject") {
      } else {
        ;
        exit(1);
      }
    } else if (c.group == "EV") {
      if (s.size() < 3) {
        ;
        exit(1);
      }
      c.command = s[2];
      if (c.command == "charge_from_grid" || c.command == "charge_to_grid" ||
          c.command == "move" || c.command == "pickup") {
        if (s.size() != 4) {
          ;
          exit(1);
        }
        c.param1 = std::stoi(s[3]);
      } else if (c.command == "stay") {
      } else {
        ;
        exit(1);
      }
    }
    commands.push_back(c);
  }
}
void judge::saveStat(StatusOnAcc &acc_stat) {
  acc_stat.grid_cap.clear();
  acc_stat.vehicle_cap.clear();
  acc_stat.vehicle_pos.clear();
  acc_stat.work_cap.clear();
  for (auto &gr : g.nodes) {
    acc_stat.grid_cap.push_back(gr.cap);
  }
  for (auto &v : vehicles) {
    acc_stat.vehicle_cap.push_back(v.cap);
    acc_stat.vehicle_pos.push_back(v.pos);
  }
  for (auto &w : work.status) {
    acc_stat.work_cap.push_back(w.charge);
  }
}
bool judge::checkBuy() {
  for (auto gr : g.nodes) {
    if (gr.L_buy > 0) {
      return true;
    }
  }
  return false;
}
void judge::do_judge(Main &main, std::vector<Command2> &commands, bool onAcc) {
  int t = T_now - 1;
  std::set<int> ev_set;
  std::set<int> fe_set;
  std::set<int> order_set;
  std::map<int, int> delta_tmp_to;
  std::map<int, int> delta_tmp_from;
  std::map<int, Command2 *> enable_commands;
  enable_commands.clear();
  for (auto &c : commands) {
    if (c.group == "Order") {
      enable_commands[c.id] = &c;
    }
  }
  for (auto &pair : enable_commands) {
    auto &c = *pair.second;
    {
      if (c.id < 0 || (int)activeOrders.size() <= c.id) {
        ;
        exit(1);
      }
      if (order_set.find(c.id) != order_set.end()) {
        ;
        exit(1);
      }
      order_set.insert(c.id);
      OrderB *o = activeOrders[c.id];
      if (o->status == 0) {
        if (c.command == "accept") {
          o->status = 1;
        } else if (c.command == "reject") {
          o->status = -1;
        } else {
          assert(false);
          exit(1);
        }
      } else {
        ;
        exit(1);
      }
    }
  }
  for (OrderB *o : activeOrders) {
    if (o->status == 0) {
      if (t - o->startTime > (int)T_grace) {
        o->status = -2;
      }
    }
  }
  enable_commands.clear();
  for (auto &c : commands) {
    if (c.group == "EV") {
      enable_commands[c.id] = &c;
    }
  }
  for (auto &pair : enable_commands) {
    auto &c = *pair.second;
    {
      if (c.id < 0 || (int)main.A_Data.vehicles.size() <= c.id) {
        ;
        exit(1);
      }
      if (ev_set.find(c.id) != ev_set.end()) {
        ;
        exit(1);
      }
      ev_set.insert(c.id);
      if (c.command == "stay") {
      } else if (c.command == "move") {
        int vertex = c.param1 - 1;
        if (!valid_move(c.id, vertex)) {
          ;
          exit(1);
        }
      } else if (c.command == "pickup") {
        int ord_id = c.param1 - 1;
        if (!valid_pickup(ord_id, c.id)) {
          ;
          exit(1);
        }
      }
      else if (c.command == "charge_from_grid") {
        int amount = c.param1;
        auto &v = vehicles[c.id];
        position &pos = v.pos;
        if (!pos.on_vertex()) {
          ;
          exit(1);
        }
        if (amount <= 0) {
          ;
          exit(1);
        }
        int vertex_id = pos.now_vertex();
        auto &current_node = g.nodes[vertex_id];
        if (!current_node.is_grid()) {
          ;
          ;
          exit(1);
        }
        if (amount > v.V_in_Max_EV) {
          ;
          exit(1);
        }
        if (v.cap + amount > v.max_cap) {
         
                                                        ;
          exit(1);
        }
        v.charge(amount);
        delta_tmp_from[vertex_id] += amount;
      }
      else if (c.command == "charge_to_grid") {
        int amount = c.param1;
        auto &v = vehicles[c.id];
        position &pos = v.pos;
        if (!pos.on_vertex()) {
          ;
          exit(1);
        }
        if (amount <= 0) {
          ;
          exit(1);
        }
        int vertex_id = pos.now_vertex();
        auto &current_node = g.nodes[vertex_id];
        if (!current_node.is_grid()) {
          ;
          ;
          exit(1);
        }
        if (amount > v.V_out_Max_EV) {
          ;
          exit(1);
        }
        if (amount > v.cap) {
         
                              ;
          exit(1);
        }
        v.consume(amount);
        delta_tmp_to[vertex_id] += amount;
      } else {
        assert(false);
        exit(1);
      }
    }
  }
  for (Grid *p : main.A_Data.grids) {
    if (p->fe != nullptr) {
      p->P_FE = 0;
    }
  }
  enable_commands.clear();
  for (auto &c : commands) {
    if (c.group == "FE") {
      enable_commands[c.id] = &c;
    }
  }
  for (auto &pair : enable_commands) {
    auto &c = *pair.second;
    {
      if (c.id < 0 || (int)N <= c.id) {
        ;
        exit(1);
      }
      Grid *p = main.A_Data.vertexToGrid[c.id];
      if (p == nullptr || p->fe == nullptr) {
        ;
        exit(1);
      }
      if (fe_set.find(c.id) != fe_set.end()) {
        ;
        exit(1);
      }
      fe_set.insert(c.id);
      p->P_FE = c.param1;
      if (p->P_FE != 0) {
        if (p->fe->P_FE_min > p->P_FE) {
         
                                ;
          exit(1);
        }
        if (p->fe->P_FE_max < p->P_FE) {
         
                                ;
          exit(1);
        }
      }
    }
  }
  enable_commands.clear();
  for (auto &c : commands) {
    if (c.group == "Machinery") {
      enable_commands[c.id] = &c;
    }
  }
  for (auto &pair : enable_commands) {
    auto &c = *pair.second;
    if (c.group == "Machinery") {
      if (c.id < 0 || (int)work.N_work <= c.id) {
        ;
        exit(1);
      }
    }
  }
  for (size_t i = 0; i < work.N_work; i++) {
    auto &w = work.status[i];
    Command2 *c = enable_commands[i];
    if (c != nullptr && c->command == "work") {
      int ts = t / (T_max / N_div);
      if (onAcc) {
        ;
        exit(1);
      }
      if (w.detail->A_work[ts] == 0) {
        ;
        exit(1);
      }
      if (w.charge < w.detail->delta_work) {
        ;
        exit(1);
      }
      if (w.yield >= w.detail->D_work) {
        ;
        exit(1);
      }
      if (w.startTime < 0) {
        w.startTime = T_now;
      }
      w.charge -= w.detail->delta_work;
      w.yield++;
    } else {
      if (w.startTime >= 0) {
        int wt = (int)T_now - w.startTime;
        if (wt < w.detail->I_work_min) {
          if (w.yield < w.detail->D_work) {
           
                                       ;
            exit(1);
          }
        }
        w.startTime = -1;
      }
      if (c != nullptr) {
        if (c->command == "charge_from") {
          int chg = c->param1;
          if (chg > w.detail->V_work_charge) {
           
                                          ;
            exit(1);
          }
          int chg2 = chg * w.detail->Eta_work / 100;
          if (chg2 + w.charge > w.detail->Cap_work_ele) {
           
                                                                    ;
            exit(1);
          }
          w.charge += chg2;
          delta_tmp_from[w.detail->x] += chg;
        } else if (c->command == "charge_to") {
          int chg = c->param1;
          if (chg > w.detail->V_work_charge) {
           
                                          ;
            exit(1);
          }
          if (chg > w.charge) {
            ;
            exit(1);
          }
          w.charge -= chg;
          delta_tmp_to[w.detail->x] += chg;
        }
      }
    }
  }
  ;
  for (auto &pair : delta_tmp_to) {
    Grid *g = main.A_Data.vertexToGrid[pair.first];
    int P = pair.second;
    if (g == nullptr || g->evc == nullptr || P > g->evc->P_EVC_in) {
      if (g == nullptr || g->evc == nullptr) {
        ;
      } else {
        ;
      }
      exit(1);
    }
  }
  for (auto &pair : delta_tmp_from) {
    Grid *g = main.A_Data.vertexToGrid[pair.first];
    int P = pair.second;
    if (g == nullptr || g->evc == nullptr || P > g->evc->P_EVC_out) {
      if (g == nullptr || g->evc == nullptr) {
        ;
      } else {
        ;
      }
      exit(1);
    }
  }
  ;
  for (size_t vertex_id = 0; vertex_id < N; vertex_id++) {
    Grid *p = main.A_Data.vertexToGrid[vertex_id];
    if (p == nullptr) {
      continue;
    }
    ;
    auto &q = g.nodes[vertex_id];
    ;
    ;
    auto &e = energies[t][p->grid_id];
    int actual = e.actual;
    if (onAcc) {
      for (auto &slt : shlt.shelter_data) {
        if (slt.x == (int)vertex_id) {
          int D_i = shlt.shelter_D[(T_now - 1) / (T_max / N_div)];
          int D_shelter = slt.p * D_i / 100;
          actual -= D_shelter;
        }
      }
    }
    q.pw_actual = actual;
    assert(p->grid_id == (int)e.id);
    int P_RB_charge = (p->rb ? p->rb->P_RB_charge : 0);
    int P_RB_discharge = (p->rb ? p->rb->P_RB_discharge : 0);
    int Eta_RB = (p->rb ? p->rb->Eta_RB : 1);
    int P_FE = p->P_FE;
    int delta_tmp =
    q.pw_actual + P_FE + delta_tmp_to[vertex_id] - delta_tmp_from[vertex_id];
    ;
    int delta_total;
    if (delta_tmp > std::min(P_RB_charge, p->Cap_RB_total - q.cap)) {
      delta_total = std::min(P_RB_charge, p->Cap_RB_total - q.cap);
      q.pw_excess = delta_tmp - delta_total;
      q.pw_buy = 0;
    } else if (delta_tmp < -std::min(P_RB_discharge, q.cap)) {
      delta_total = -std::min(P_RB_discharge, q.cap);
      q.pw_excess = 0;
      q.pw_buy = delta_total - delta_tmp;
    } else {
      delta_total = delta_tmp;
      q.pw_excess = 0;
      q.pw_buy = 0;
    }
    int effective_delta = delta_total * Eta_RB / 100;
    if (effective_delta < 0)
      q.cap += delta_total;
    else
      q.cap += effective_delta;
    const double eta_FE = p->fe and p->fe->Eta_FE_min > 0
                          ? 100.0 * ((p->P_FE - p->fe->P_FE_min) *
                                     (p->fe->Eta_FE_max - p->fe->Eta_FE_min) /
                                     (p->fe->P_FE_max - p->fe->P_FE_min) +
                                     p->fe->Eta_FE_min)
                          : 1;
    q.L_FE = eta_FE * p->P_FE;
    q.L_buy = q.pw_buy;
  }
}
double run_alg(const bool submitFlag,
               std::vector<std::string> &args,
               judge &Common,
               FILE *,
               const size_t day,
               StatusOnAcc *acc_stat) {
  ;
  if (false) fprintf(stderr, "###Debug >>>run_alg(submitFlag=%d)\n",
                      submitFlag);
  if (acc_stat) {
   
                                             ;
  } else {
    ;
  }
  Main main;
  std::string result =
  Common.set_Algorithm_Initial_Input1(submitFlag, day, args, main, acc_stat);
  if (result == "WA") {
    exit(1);
  }
  bool ignore_order = false;
  if (acc_stat != NULL && acc_stat->acc_mode) {
    ignore_order = true;
  }
  Common.set_Algorithm_Initial_Input2(submitFlag, main, day, ignore_order);
  Common.T_now = 0;
  judge &Judge = Common;
  if (false) fprintf(stderr, "###Debug Common.T_max=%zu,Judge.T_max=%zu\n",
                      Common.T_max, Judge.T_max);
  double ele_score = 0;
  double env_score = 0;
  double C_grid_0 = Judge.current_all_grid_charge();
  double C_EV_0 = Judge.current_all_EV_charge(main);
  bool onAcc = (acc_stat != nullptr && acc_stat->acc_mode);
  if (onAcc) {
    for (auto &slt : Common.shlt.shelter_data) {
      Grid *grd = main.A_Data.vertexToGrid[slt.x];
      if (grd == nullptr || !grd->is_nano) {
        ;
        return 1;
      }
    }
  }
  for (size_t t = 0; t < Judge.T_max; t++) {
    if (t % 500 == 0) {
      ;
      ;
    }
    Judge.next_time_step();
    std::string out = Judge.run_Algorithm(submitFlag, main, t, day, onAcc);
    if (false) {
      for (size_t i = 0; i < Judge.g.nodes.size(); i++) {
        if (main.A_Data.vertexToGrid[i] || Judge.g.nodes[i].pw_buy > 0) {
          auto &node = Judge.g.nodes[i];
         
                                      ;
        }
      }
      for (size_t i = 0; i < main.A_Data.grids.size(); i++) {
        Grid &grid = *main.A_Data.grids[i];
       
                                              ;
      }
      for (size_t i = 0; i < Judge.vehicles.size(); i++) {
        auto &v = Judge.vehicles[i];
       
                                                   ;
      }
      for (size_t i = 0; i < main.A_Data.vehicles.size(); i++) {
        Vehicle *v = main.A_Data.vehicles[i];
       
                                      ;
      }
    }
    ele_score += Judge.current_electricity_score();
    env_score += Judge.current_env_score();
    if (acc_stat != NULL && acc_stat->Day_acc == day && acc_stat->T_acc == t) {
      Judge.saveStat(*acc_stat);
    }
    if (acc_stat != NULL && acc_stat->acc_mode) {
      if (Judge.checkBuy()) {
        ;
        return 1;
      };
    }
  }
  if (acc_stat != NULL && acc_stat->acc_mode) {
    Judge.saveStat(*acc_stat);
    ;
    return 0;
  }
  double C_grid_tmax = Judge.current_all_grid_charge();
  double C_EV_tmax = Judge.current_all_EV_charge(main);
  double C_EV_return = Judge.current_all_EV_return(main);
  ;
  double trans_score = Judge.transport_score(main);
  double C_balance = C_EV_tmax + C_grid_tmax - C_grid_0 - C_EV_0 - C_EV_return;
  if (false) fprintf(stderr, "###C_blance: %f %f %f %f %f\n", C_EV_tmax,
                      C_grid_tmax, C_grid_0, C_EV_0, C_EV_return);
  ;
  ele_score = Judge.electricity_score(C_balance, ele_score);
  double work_score = Judge.work_score();
 
                                        ;
  if (!submitFlag) {
    fprintf(stdout, "%lf %lf %lf %lf\n", trans_score, ele_score, env_score,
            work_score);
    if (Common.outlog_fp) {
      fprintf(Common.outlog_fp, "%lf %lf %lf %lf\n", trans_score, ele_score,
              env_score, work_score);
    }
  }
  ;
  if (false) fprintf(stderr, "###Debug <<<run_alg(submitFlag=%d)\n",
                      submitFlag);
  int day_score =
  Judge.calc_day_score(day, trans_score, ele_score, env_score, work_score);
  return day_score;
}
double main2() {
  std::string cmd;
  std::vector<score2> Answers;
  score2 base;
  judge Common;
  Common.open_outlog();
  FILE *fp, *contestant_output, *time_step_result;
  fp = stdin;
  contestant_output = stdout;
  time_step_result = stdout;
  ;
  Common.readInput1(fp);
  reactive_connect();
  ;
  ;
  while (true) {
    Common.readLineSkipComment();
    std::string cmd = Common.StrLine;
    ;
    if (Common.StrLine == TEXT_end) {
      break;
    }
    if (false) fprintf(stderr, "###Debug %s(%d),cmd=[%s]\n", "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp",
                        3737, cmd.c_str());
    Common.processQueryCommand(cmd, contestant_output);
    fflush(contestant_output);
  }
  double total_score = 0.0;
  std::vector<std::string> cmd_args;
  bool submitFlg = false;
  for (;;) {
    Common.readInput2(fp)
    ;
    Common.readLineSkipComment();
    cmd = Common.StrLine;
    if (false) fprintf(stderr, "###Debug %s(%d),cmd=%s\n", "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp", 3759,
                        cmd.c_str());
    int argc = StringHelper::SplitToken(cmd, " ", cmd_args);
    if (false) fprintf(stderr, "###Debug %s(%d),argc=%d\n", "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp", 3762,
                        argc);
    for (int i = 0; i < argc; i++) {
      if (false) fprintf(stderr, "###Debug arg[%d]=%s\n", i,
                          cmd_args[i].c_str());
    }
    if (argc < 2) {
      ;
      exit(1);
    }
    int day = std::stoi(cmd_args[1]);
    std::vector<std::string> args;
    for (int i = 2; i < argc; ++i)
      args.emplace_back(cmd_args[i]);
    ;
    if (cmd_args[0] == "test") {
      ;
      if (!Common.checkRange(day, 1, true, Common.N_day, true)) {
        if (false) fprintf(stderr, "###Debug 6-1 invalid day in command:%s\n",
                            cmd.c_str());
        exit(1);
      }
      day -= 1;
      ;
      ;
      double test_score =
      run_alg(false, args, Common, time_step_result, day, NULL);
      ;
      fflush(contestant_output);
    } else if (cmd_args[0] == "submit") {
      ;
      random_helper.set_seed(SUBMIT_SEED);
      ;
      submitFlg = true;
      int Day_acc = random_helper.nextInt(Common.N_day);
      int T_acc = random_helper.nextInt(Common.T_max);
      StatusOnAcc acc_stat(Day_acc, T_acc);
      if (false) fprintf(stderr, "###Debug %s(%d),Common.N_day=%zu\n",
                          "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp", 3811, Common.N_day);
      for (size_t i = 0; i < Common.N_day; i++) {
        if (false) fprintf(stderr, "###Debug %s(%d),i=%zu\n", "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp",
                            3814, i);
        ;
        double day_score =
        run_alg(true, args, Common, time_step_result, i, &acc_stat);
        ;
        ;
        total_score += day_score;
      }
      size_t Acc_Day_max = Common.N_acc;
      int S_acc_Day = 0;
      acc_stat.acc_mode = true;
      for (size_t i = 0; i < Acc_Day_max; i++) {
        ;
        double use_buy =
        run_alg(true, args, Common, time_step_result, Day_acc, &acc_stat);
        ;
        if (use_buy > 0) {
          break;
        } else {
          S_acc_Day++;
        }
      }
      ;
      double acc_score = Common.curr_score.alpha_acc * S_acc_Day;
      ;
      total_score += Common.curr_score.w_acc * acc_score;
      total_score -= 1.0 * Common.curr_score.alpha_cost *
                     std::max(0, Common.C_total - Common.C_init);
      if (Common.outlog_fp) {
        fprintf(Common.outlog_fp, "#Total Score\n");
        fprintf(Common.outlog_fp, "%lf\n", total_score);
      }
    }
    else {
      if (false) fprintf(
      stderr, "###Debug %s(%d),cmd_args[0]=%s, ERROR this isn't defined\n",
      "./tmp.upload.172309.0EK1Xn/judge_B/judge_B.cpp", 3859, cmd_args[0].c_str());
      exit(1);
    }
    ;
    if (submitFlg) {
      break;
    }
  }
  sleep(1);
  reactive_disconnect();
  return std::max(1.0, total_score);
}
int main(int argc, char **argv) {
  reactive_start(argc, (char *const *)argv);
  ;
  double ans = main2();
  ;
  printf("%0.2lf\n", ans);
  fflush(stdout);
  ;
  guard.is_accepted = true;
  reactive_end();
  return 0;
}
