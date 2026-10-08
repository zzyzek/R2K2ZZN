// To the extent possible under law, the person who associated CC0 with
// this project has waived all copyright and related or neighboring rights
// to this project.
//
// You should have received a copy of the CC0 legalcode along with this
// work. If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

var CANVAS_ID = 'twojs_canvas';

var COLOR = [
    "rgb(152,119,182)",
    "rgb(228,220,242)"
];


var g_fig_ctx = {

  "uniq_id_base": "customid_",
  "uniq_id_idx": 0,
  "postprocess": [],

  "html_id":"fig",
  "two": new Two({fitted:true}),

  "pal" : [
    [47,55,55], // black
    [67,54,51], // brown

    [242,244,203], // beige
    [255,94,91], // red
    [197,40,61], // other red

    [255,200,87], // yellow
    [233,114,76], // orange

    [155,195,212], // dark blue
    [164,216,224], // mid blue
    [168,225,230], // light blue

    [100,185,106], // hot green

    [139,177,116], // dark green
    [147,182,126],  // mid green
    [167,196,151]  // light green
  ],

  "rgba_pal" : [
    ""
  ],

  "geom":[],

};


function _dl() {
  var ele = document.getElementById(CANVAS_ID);
  var b = new Blob([ ele.innerHTML ]);
  saveAs(b, "fig.svg");
}

function makeTwoVector(_pnt) {
  let pnt = [];
  for (let ii=0; ii<_pnt.length; ii++) {
    pnt.push( new Two.Vector(_pnt[ii][0], _pnt[ii][1]) );
  }
  return pnt;
}

function makeTwoAnchor(_pnt) {
  let pnt = [];
  for (let ii=0; ii<_pnt.length; ii++) {
    pnt.push( new Two.Anchor(_pnt[ii][0], _pnt[ii][1]) );
  }
  return pnt;
}

function mk_checkerboard_endpoints(opt) {
  let two = g_fig_ctx.two;

  let sx = opt.sx;
  let sy = opt.sy;

  let nx = opt.nx;
  let ny = opt.ny;

  let x_len = opt.x_len;
  let y_len = opt.y_len;

  let color_scheme = {
    "red-beige": [ [248,112,116], [248,235,187] ],
    "purple-light" : [[ 152,119,182], [228,220,242] ],
    "green-yellow": [  [85,149,100], [236,249, 179] ],
    "grey-light" : [ [142,162,172], [224,226,231] ]
  };

  let color = [
    "rgba(152,119,182,0.5)",
    "rgba(228,220,242,0.5)"
  ];

  color = [
    "rgb(152,119,182)",
    "rgb(228,220,242)"
  ];

  color = COLOR;

  let fudge_parity = ((nx*ny)%2);
  fudge_parity = 0;
  if ("initial_parity" in opt) {
    fudge_parity = opt.initial_parity;
  }


  for (let iy = 0; iy < ny; iy++) {
    for (let ix = 0; ix < nx; ix++) {

      let parity = (ix+iy +fudge_parity)%2;

      let x = sx + ix*x_len;
      let y = sy + iy*y_len;
      let rect = new Two.Rectangle( x,y, x_len, y_len );
      rect.linewidth = 0.5;

      rect.stroke = "rgba(0,0,0,0.4)";
      rect.fill = "rgba(255, 200, 200, 1)";
      rect.fill = color[ parity ];

      rect.stroke = "rgb(0,0,0)";
      rect.fill = color[parity];
      rect.opacity = 0.5;

      two.add(rect);

    }
  }

  //let path_r = 8.5;
  let cr = (("c_rad" in opt) ? opt.c_rad : 8.5);
  let lw = (("l_width" in opt) ? opt.l_width : 10);

  let path_colors = [
    "rgb(80,80,140)",
    "rgb(200,60,50)"
  ];

  for (let s_idx=0; s_idx < opt.S.length; s_idx++) {

    let ep_color = path_colors[s_idx];

    let spos = opt.S[s_idx];
    let tpos = opt.T[s_idx];

    let s_p = [ sx + spos[0]*x_len, sy + spos[1]*y_len ];
    let t_p = [ sx + tpos[0]*x_len, sy + tpos[1]*y_len ];

    let start_circle = two.makeCircle( s_p[0], s_p[1], cr );
    start_circle.fill = ep_color;
    start_circle.linewidth = 0;
    start_circle.stroke = ep_color;

    let end_circle = two.makeCircle( t_p[0], t_p[1], cr );
    end_circle.fill = ep_color;
    end_circle.linewidth = 0;
    end_circle.stroke = ep_color;
  }

  if (("overlay" in opt) &&
      (typeof opt.overlay !== "undefined")) {
    let overlay_color = opt.overlay;
    let overlay_opacity = (("overlay_opacity" in opt) ? opt.overlay_opacity : 0.25);

    let sx2 = (nx*x_len/2) - (x_len/2);
    let sy2 = (ny*y_len/2) - (y_len/2);

    let r = two.makeRectangle( sx + sx2,sy + sy2, nx*x_len, ny*y_len );
    r.fill = overlay_color;
    r.opacity = overlay_opacity;
  }

  two.update();
}

function mk_paths(opt) {
  let two = g_fig_ctx.two;

  let sx = opt.sx;
  let sy = opt.sy;

  let nx = opt.nx;
  let ny = opt.ny;

  let x_len = opt.x_len;
  let y_len = opt.y_len;

  let color_scheme = {
    "red-beige": [ [248,112,116], [248,235,187] ],
    "purple-light" : [[ 152,119,182], [228,220,242] ],
    "green-yellow": [  [85,149,100], [236,249, 179] ],
    "grey-light" : [ [142,162,172], [224,226,231] ]
  };

  let color = [
    "rgba(152,119,182,0.5)",
    "rgba(228,220,242,0.5)"
  ];

  color = [
    "rgb(152,119,182)",
    "rgb(228,220,242)"
  ];

  let fudge_parity = ((nx*ny)%2);
  if ("initial_parity" in opt) {
    fudge_parity = opt.initial_parity;
  }

  let lw = (("l_width" in opt) ? opt.l_width : 10);
  let cr = (("c_rad" in opt) ? opt.c_rad : 8.5);

  let path_color = "rgba(60,60,120,1)";

  path_color = "rgba(80,80,140,1)";
  path_color = "rgb(80,80,140)";

  let path_colors = [
    "rgb(80,80,140)",
    "rgb(200,60,50)"
  ];

  let show_start_circle = false,
      show_end_circle = false;



  let paths = opt.paths;

  for (let path_idx=0; path_idx<paths.length; path_idx++) {
    let _p = paths[path_idx];
    let w_p = [];
    for (let idx = 0; idx < _p.length; idx++) {
      w_p.push( [ sx + _p[idx][0]*x_len, sy + _p[idx][1]*y_len ] );
    }

    if (w_p.length == 0) { continue; }

    path_color = path_colors[path_idx];

    let np_center = {};
    if (("nopath" in opt) &&
        (opt.nopath)) {
      np_center = w_p.pop();
    }

    let tv_path = makeTwoVector(w_p);
    let t_path = two.makePath(tv_path, true);

    t_path.noFill();
    t_path.linewidth = lw;
    t_path.stroke = path_color;
    t_path.cap = 'round';
    t_path.join = 'round';

    if (show_start_circle) {
      let start_circle = two.makeCircle( w_p[0][0], w_p[0][1], cr );
      start_circle.fill = path_color;
      start_circle.linewidth = 0;
      start_circle.stroke = path_color;
    }

    if (show_end_circle) {
      if (("end_circle" in opt) &&
          (opt.end_circle)) {
        let n = w_p.length-1;
        let end_circle = two.makeCircle( w_p[n][0], w_p[n][1], cr );
        //end_circle.fill = "rgba(120,120,240,1)";
        end_circle.fill = path_color;
        end_circle.linewidth = 0;
        end_circle.stroke = path_color;
      }
    }
  }

  two.update();
}


function mk_checkerboard_paths(opt) {
  let two = g_fig_ctx.two;

  let sx = opt.sx;
  let sy = opt.sy;

  let nx = opt.nx;
  let ny = opt.ny;

  let x_len = opt.x_len;
  let y_len = opt.y_len;

  let color_scheme = {
    "red-beige": [ [248,112,116], [248,235,187] ],
    "purple-light" : [[ 152,119,182], [228,220,242] ],
    "green-yellow": [  [85,149,100], [236,249, 179] ],
    "grey-light" : [ [142,162,172], [224,226,231] ]
  };

  let color = [
    "rgba(152,119,182,0.5)",
    "rgba(228,220,242,0.5)"
  ];

  color = [
    "rgb(152,119,182)",
    "rgb(228,220,242)"
  ];

  color = COLOR;

  let fudge_parity = ((nx*ny)%2);
  if ("initial_parity" in opt) {
    fudge_parity = opt.initial_parity;
  }


  for (let iy = 0; iy < ny; iy++) {
    for (let ix = 0; ix < nx; ix++) {

      let parity = (ix+iy +fudge_parity)%2;

      let x = sx + ix*x_len;
      let y = sy + iy*y_len;
      let rect = new Two.Rectangle( x,y, x_len, y_len );
      rect.linewidth = 0.5;

      rect.stroke = "rgba(0,0,0,0.4)";
      rect.fill = "rgba(255, 200, 200, 1)";
      rect.fill = color[ parity ];

      rect.stroke = "rgb(0,0,0)";
      rect.fill = color[parity];
      rect.opacity = 0.5;

      two.add(rect);

    }
  }

  let lw = (("l_width" in opt) ? opt.l_width : 10);
  let cr = (("c_rad" in opt) ? opt.c_rad : 8.5);

  let path_color = "rgba(60,60,120,1)";

  path_color = "rgba(80,80,140,1)";
  path_color = "rgb(80,80,140)";

  let path_colors = [
    "rgb(80,80,140)",
    "rgb(200,60,50)"
  ];


  let paths = opt.paths;

  for (let path_idx=0; path_idx<paths.length; path_idx++) {
    let _p = paths[path_idx];
    let w_p = [];
    for (let idx = 0; idx < _p.length; idx++) {
      w_p.push( [ sx + _p[idx][0]*x_len, sy + _p[idx][1]*y_len ] );
    }

    if (w_p.length == 0) { continue; }

    path_color = path_colors[path_idx];

    let np_center = {};
    if (("nopath" in opt) &&
        (opt.nopath)) {
      np_center = w_p.pop();
    }

    let tv_path = makeTwoVector(w_p);
    let t_path = two.makePath(tv_path, true);

    t_path.noFill();
    t_path.linewidth = lw;
    t_path.stroke = path_color;
    t_path.cap = 'round';
    t_path.join = 'round';

    let start_circle = two.makeCircle( w_p[0][0], w_p[0][1], cr );
    start_circle.fill = path_color;
    start_circle.linewidth = 0;
    start_circle.stroke = path_color;

    if (("end_circle" in opt) &&
        (opt.end_circle)) {
      let n = w_p.length-1;
      let end_circle = two.makeCircle( w_p[n][0], w_p[n][1], cr );
      //end_circle.fill = "rgba(120,120,240,1)";
      end_circle.fill = path_color;
      end_circle.linewidth = 0;
      end_circle.stroke = path_color;
    }
  }

  two.update();
}

function _get_overlay(ctx) {

  let stst = [];
  let grid = [];

  let CUTOFF_OVERLAY = "rgb(20,40,80)";
  let CORNER_OVERLAY = "rgb(80,40,20)";
  let SQUARE_OVERLAY = "rgb(40,20,80)";

  //---
  // grid for easy access

  let wh = ctx.size;
  for (let j=0; j<wh[1]; j++) {
    grid.push([]);
    for (let i=0; i<wh[0]; i++) {
      grid[j].push(-1);
    }
  }

  for (let i=0; i<ctx.s.length; i++) {
    let s = ctx.s[i];
    let t = ctx.t[i];

    grid[ s[1] ][ s[0] ] = i;
    grid[ t[1] ][ t[0] ] = i;
  }


  // perimieter cutoff test
  //

  let p = [1,0];

  for (let i=1; i<wh[0]; i++) {
    let v = grid[ p[1] ][ p[0] ];
    if (v >= 0) { stst.push( v ); }
    p[0] += 1;
  }

  p = [wh[0]-1, 1];
  for (let i=1; i<wh[1]; i++) {
    let v = grid[ p[1] ][ p[0] ];
    if (v >= 0) { stst.push( v ); }
    p[1] += 1;
  }

  p = [wh[0]-2, wh[1]-1];
  for (let i=1; i<wh[0]; i++) {
    let v = grid[ p[1] ][ p[0] ];
    if (v >= 0) { stst.push( v ); }
    p[0] -= 1;
  }

  p = [0, wh[1]-2];
  for (let i=1; i<wh[1]; i++) {
    let v = grid[ p[1] ][ p[0] ];
    if (v >= 0) { stst.push( v ); }
    p[1] -= 1;
  }

  if (stst.length == 4) {
    let found = true;
    for (let i=0; i<4; i++) {
      if (stst[(i+1)%4] == stst[i]) { found=false; break; }
    }
    if (found) { return CUTOFF_OVERLAY; }
  }

  //---
  //---

  let u = grid[0][0],
      v = grid[0][1],
      w = grid[1][0];


  if ( (u<0) && (v>=0) && (w>=0) && (v!=w) ) { return CORNER_OVERLAY; }

  u = grid[wh[1]-1][0];
  v = grid[wh[1]-1][1];
  w = grid[wh[1]-2][0];

  if ( (u<0) && (v>=0) && (w>=0) && (v!=w) ) { return CORNER_OVERLAY; }

  u = grid[wh[1]-1][wh[0]-1];
  v = grid[wh[1]-1][wh[0]-2];
  w = grid[wh[1]-2][wh[0]-1];

  if ( (u<0) && (v>=0) && (w>=0) && (v!=w) ) { return CORNER_OVERLAY; }

  u = grid[0][wh[0]-1];
  v = grid[0][wh[0]-2];
  w = grid[1][wh[0]-1];

  if ( (u<0) && (v>=0) && (w>=0) && (v!=w) ) { return CORNER_OVERLAY; }

  //--

  for (let j=0; j<(wh[1]-1); j++) {
    for (let i=0; i<(wh[0]-1); i++) {
      let u00 = grid[j][i];
      let u10 = grid[j][i+1];
      let u01 = grid[j+1][i];
      let u11 = grid[j+1][i+1];

      if ((u00 < 0) || (u10 < 0) ||
          (u01 < 0) || (u11 < 0)) { continue; }

      if ((u00 == u11) && (u10 == u01)) {
        return SQUARE_OVERLAY;
      }
    }
  }

  return undefined;
}

function canvas_init() {

  let square_size = 40;
  let sx = 50,
      sy = 50;

  let l_width = square_size / 3,
      c_rad = square_size * 17/60;

  let path = [
    [ [0,0], [0,1], [0,2] ],
    [ [1,0], [1,1], [1,2],
      [2,2], [2,1], [2,0] ]
  ];

  let opt = {
    "nx": 3, "ny": 3,

    "sx": sx, "sy": sy,

    "l_width": l_width,
    "end_circle": true,
    "c_rad" : c_rad,
    "x_len": square_size, "y_len" : square_size,

    "S": [ [0,0], [1,0] ],
    "T": [ [0,2], [2,0] ],

    "paths": path

  };

  let tv = -1, tv2 = [-1,-1];

  tv = _get_ivalu( "ui_nx" );
  if (typeof tv!== "undefined") { opt.nx = tv; }

  tv = _get_ivalu( "ui_ny" );
  if (typeof tv!== "undefined") { opt.ny = tv; }

  tv2 = _get_v2valu( "ui_s0" );
  if (typeof tv2 !== "undefined") { opt.S[0] = tv2; }

  tv2 = _get_v2valu( "ui_t0" );
  if (typeof tv2 !== "undefined") { opt.T[0] = tv2; }

  tv2 = _get_v2valu( "ui_s1" );
  if (typeof tv2 !== "undefined") { opt.S[1] = tv2; }

  tv2 = _get_v2valu( "ui_t1" );
  if (typeof tv2 !== "undefined") { opt.T[1] = tv2; }

 
  mk_checkerboard_endpoints(opt);
}

function _get_ui_paths( ui_id ) {
  let ele = document.getElementById(ui_id);
  let txt = ele.value;

  let data = [ [], [] ];

  try {
    data = JSON.parse(txt);
  }
  catch (e) {
    //console.log("e:", e);
  }

  return data;
}

function _get_ival( ui_id ) {
  let ele = document.getElementById(ui_id);
  if (ele.value == "") { return 0; }
  return parseInt(ele.value);
}

function _get_ivalu( ui_id ) {
  let ele = document.getElementById(ui_id);
  if (ele.value == "") { return undefined; }
  return parseInt(ele.value);
}

function _get_v2val( ui_id ) {
  let v2 = [0,0];
  let ele = document.getElementById(ui_id);
  let tok = ele.value.trim().replace(/,/g, ' ').replace( /  */g, ' ' ).split(" ");
  if (tok.length > 0) {
    v2[0] = parseInt(tok[0]);
    if (tok.length > 1) {
      v2[1] = parseInt(tok[1]);
    }
  }
  return v2;
}

function _get_v2valu( ui_id ) {
  let v2 = [0,0];
  let ele = document.getElementById(ui_id);
  let tok = ele.value.trim().replace(/,/g, ' ').replace( /  */g, ' ' ).split(" ");
  if (tok.length != 2) { return undefined; }
  if (tok.length > 0) {
    v2[0] = parseInt(tok[0]);
    if (tok.length > 1) {
      v2[1] = parseInt(tok[1]);
    }
  }
  return v2;
}

function _check_instance(opt) {
  let nx = opt.nx;
  let ny = opt.ny;
  let stst = [ opt.S[0], opt.T[0], opt.S[1], opt.T[1] ];

  for (let i=0; i<stst.length; i++) {
    let v = stst[i];
    if ((v[0] < 0) || (v[0] >= nx) ||
        (v[1] < 0) || (v[1] >= ny)) { return -1; }

    for (let j=(i+1); j<stst.length; j++) {
      let u = stst[j];

      if ((v[0] == u[0]) && (v[1] == u[1])) { return -2; }
    }
  }

  return 0;
}

function _display_message(state, msg) {
  state = ((typeof state === "undefined") ? 0 : state);
  msg = ((typeof msg === "undefined") ? "" : msg);

  let ele = document.getElementById("ui_btn_msg");
  ele.value = msg;

  if (state < 0) {
    ele.style.display = 'block';
    ele.style.backgroundColor = "rgb(250,50,20)";
    ele.style.color = 'rgb(245,245,245)';
  }
  else if (state == 1) {
    ele.style.display = 'block';
    ele.style.backgroundColor = "rgb(230,230,10)";
    ele.style.color = 'rgb(20,20,20)';
  }

  else {
    ele.style.display = 'none';
  }

}

function ui_input(btn_id) {
  let two = g_fig_ctx.two;

  let square_size = 40;
  let sx = 50,
      sy = 50;

  let l_width = square_size / 3,
      c_rad = square_size * 17/60;

  let _opt = {
    "nx": 3, "ny": 3,

    "sx": sx, "sy": sy,

    "l_width": l_width,
    "end_circle": true,
    "c_rad" : c_rad,
    "x_len": square_size, "y_len" : square_size,

    "S": [ [0,0], [0,0] ],
    "T": [ [0,0], [0,0] ],

    "paths": []

  };


  if (btn_id == "ui_btn_render") {

    _opt.nx = _get_ival("ui_nx");
    _opt.ny = _get_ival("ui_ny");
    _opt.S[0] = _get_v2val("ui_s0");
    _opt.T[0] = _get_v2val("ui_t0");
    _opt.S[1] = _get_v2val("ui_s1");
    _opt.T[1] = _get_v2val("ui_t1");

    _opt.paths = _get_ui_paths( "ui_path" );

    two.clear();
    mk_checkerboard_endpoints(_opt);
    mk_paths(_opt);
    two.update();

    if (_check_instance(_opt) < 0) {
      _display_message(-1, "bad input");
      return;
    }
    _display_message(0);


  }

  else if (btn_id == "ui_btn_solve") {

    _opt.nx = _get_ival("ui_nx");
    _opt.ny = _get_ival("ui_ny");
    _opt.S[0] = _get_v2val("ui_s0");
    _opt.T[0] = _get_v2val("ui_t0");
    _opt.S[1] = _get_v2val("ui_s1");
    _opt.T[1] = _get_v2val("ui_t1");

    if (_check_instance(_opt) < 0) {
      _display_message(-1, "bad input");
      return;
    }
    _display_message(0);

    // solver expects in [row,column], so entries are flipped
    // from how we think about them in the viz.
    //
    let I = {
      "R" : _opt.ny,
      "C" : _opt.nx,
      "s0": [ _opt.S[0][1], _opt.S[0][0] ],
      "t0": [ _opt.T[0][1], _opt.T[0][0] ],
      "s1": [ _opt.S[1][1], _opt.S[1][0] ],
      "t1": [ _opt.T[1][1], _opt.T[1][0] ]
    };
    let s = zzn.solve(I);
    _opt.paths = [ [], [] ];


    let path_txt = "[ [], [] ]";
    if (s !== null) {

      // flip path back for viz
      //
      let viz_path = [ [], [] ];
      for (let k=0; k<2; k++) {
        for (let i=0; i<s[k].length; i++) {
          viz_path[k].push( [ s[k][i][1], s[k][i][0] ] );
        }
      }

      _opt.paths = viz_path;
      //path_txt = "[ " + JSON.stringify(s[0]) + ",\n" +
      //  "  " + JSON.stringify(s[1]) + " ]\n";
      path_txt = "[ " + JSON.stringify(viz_path[0]) + ",\n" +
        "  " + JSON.stringify(viz_path[1]) + " ]\n";
      _display_message(0);
    }
    else {
      _display_message(1, "no soln");
    }

    let ele = document.getElementById("ui_path");
    ele.value = path_txt;

    two.clear();

    if (s !== null) { mk_checkerboard_paths(_opt); }
    else            { mk_checkerboard_endpoints(_opt); }

    two.update();
  }
  else if (btn_id == "ui_btn_dl") {
    _dl();
  }

  else if (btn_id == "ui_btn_random") {

    let _max_retry = 100;
    for (let _retry = 0; _retry < _max_retry; _retry++) {

      let nx = Math.floor( 2 + 10*Math.random() );
      let ny = Math.floor( 2 + 10*Math.random() );

      let s0 = [ _rnd(nx), _rnd(ny) ];
      let t0 = [ _rnd(nx), _rnd(ny) ];

      let s1 = [ _rnd(nx), _rnd(ny) ];
      let t1 = [ _rnd(nx), _rnd(ny) ];

      let _sgn = (p) => ((p[0] + p[1]) % 2 === 0 ? 1 : -1);
      let _parityOk = (R, C, pts) => pts.reduce((a, q) => a + _sgn(q[0]), 0) === 2 * ((R * C) % 2);

      _opt.nx = nx;
      _opt.ny = ny;
      _opt.S[0] = s0;
      _opt.T[0] = t0;
      _opt.S[1] = s1;
      _opt.T[1] = t1;

      if (_check_instance(_opt) < 0) { continue; }
      if (!_parityOk(nx,ny, [[s0,0],[t0,0],[s1,1],[t1,1]])) { continue; }

      let ele = document.getElementById("ui_nx");
      ele.value = nx.toString();

      ele = document.getElementById("ui_ny");
      ele.value = ny.toString();

      ele = document.getElementById("ui_s0");
      ele.value = s0[0].toString() + " " + s0[1].toString();

      ele = document.getElementById("ui_t0");
      ele.value = t0[0].toString() + " " + t0[1].toString();

      ele = document.getElementById("ui_s1");
      ele.value = s1[0].toString() + " " + s1[1].toString();

      ele = document.getElementById("ui_t1");
      ele.value = t1[0].toString() + " " + t1[1].toString();

      break;
    }

    two.clear();
    mk_checkerboard_endpoints(_opt);
    two.update();

    if (_check_instance(_opt) < 0) {
      _display_message(-1, "bad input");
      return;
    }
    _display_message(0);
  }

}

function _rnd(a) {
  return Math.floor( Math.random() * a );
}

function cb_preset() {
  console.log("...");

  let ele = document.getElementById("ui_preset");
  console.log(">>>", ele.value);
}

function web_init() {
  let two = g_fig_ctx.two;

  var ele = document.getElementById(CANVAS_ID);
  two.appendTo(ele);

  canvas_init();
  two.update();

  let ui_preset = document.getElementById("ui_preset");
  ui_preset.addEventListener("change", function(ev) { cb_preset(); });
}
