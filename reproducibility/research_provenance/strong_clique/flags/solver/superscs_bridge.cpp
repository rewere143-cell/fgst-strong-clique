// A deliberately small C ABI around the already installed CasADi SuperSCS.
// No solver is downloaded or installed. See README.md for cone conventions.
#include <superscs/scs.h>
#include <superscs/linsys/amatrix.h>
#include <cstdint>
#include <cstring>

static_assert(sizeof(scs_int) == sizeof(int64_t), "SuperSCS uses 64-bit indices");
static_assert(sizeof(scs_float) == sizeof(double), "SuperSCS uses doubles");

extern "C" const char *native_scs_version() { return scs_version(); }

extern "C" int64_t native_scs_solve(
    int64_t m, int64_t n, double *ax, int64_t *ai, int64_t *ap,
    double *b, double *c, int64_t f, int64_t l,
    int64_t nq, int64_t *q, int64_t ns, int64_t *s,
    double eps, int64_t max_iters, double max_seconds, int64_t verbose,
    int64_t super_scs, int64_t normalize, double scale, double rho_x,
    int64_t memory, int64_t warm_start, double alpha, double cg_rate,
    double *out_x, double *out_y, double *out_s,
    double *out_stats, int64_t *out_ints, char *out_status) {
  ScsAMatrix a{};
  a.x = ax; a.i = reinterpret_cast<scs_int *>(ai);
  a.p = reinterpret_cast<scs_int *>(ap); a.m = m; a.n = n;
  ScsSettings settings{};
  ScsData data{};
  data.m = m; data.n = n; data.A = &a; data.b = b; data.c = c;
  data.stgs = &settings;
  scs_set_default_settings(&data);
  settings.eps = eps; settings.max_iters = max_iters;
  settings.max_time_milliseconds = 1000.0 * max_seconds;
  settings.verbose = verbose; settings.do_super_scs = super_scs;
  settings.normalize = normalize; settings.scale = scale;
  settings.rho_x = rho_x; settings.memory = memory;
  settings.warm_start = warm_start; settings.do_record_progress = 0;
  settings.alpha = alpha; settings.cg_rate = cg_rate;
  ScsCone cone{};
  cone.f = f; cone.l = l;
  cone.q = reinterpret_cast<scs_int *>(q); cone.qsize = nq;
  cone.s = reinterpret_cast<scs_int *>(s); cone.ssize = ns;
  ScsSolution sol{};
  sol.x = out_x; sol.y = out_y; sol.s = out_s;
  ScsInfo *info = scs_init_info();
  if (!info) return -99;
  scs_int result = scs(&data, &cone, &sol, info);
  std::memcpy(out_status, info->status, SCS_INFO_STATUS_MSG_LENGTH);
  out_status[SCS_INFO_STATUS_MSG_LENGTH - 1] = '\0';
  out_ints[0] = info->iter;
  out_ints[1] = info->statusVal;
  out_ints[2] = info->cg_total_iters;
  out_stats[0] = info->pobj; out_stats[1] = info->dobj;
  out_stats[2] = info->resPri; out_stats[3] = info->resDual;
  out_stats[4] = info->resInfeas; out_stats[5] = info->resUnbdd;
  out_stats[6] = info->relGap; out_stats[7] = info->setupTime;
  out_stats[8] = info->solveTime;
  out_stats[9] = info->linsys_total_solve_time_ms;
  out_stats[10] = static_cast<double>(info->allocated_memory);
  scs_free_info(info);
  return result;
}
